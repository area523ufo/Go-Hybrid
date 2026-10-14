//! shape.rs — the lightweight TypeShape inference (NOT a type system).
//!
//! Resolves a `TypeShape` from a declared `TypeExpr` (params, `var`/`let`
//! ascriptions) or from an initializer expression (defines, loop variables),
//! consulting the file-level struct/fn/const tables and the builtin foreign
//! tables in foreign.rs. Everything unresolvable degrades to `Unknown`,
//! which is FAIL-CLOSED at spawn/send boundaries (O4.9): an unproven shape
//! may not silently cross (HYB-E3005) — but remains legal inside a function,
//! where no boundary is involved. Fewer unknowns is still the goal: the
//! inference below deliberately widens coverage (closures, option, chan
//! elements) so honest programs classify without ceremony.

use crate::foreign;
use crate::model::{Checker, FnState, TypeShape};
use hy_syntax::{BinOp, CallArg, Expr, TypeExpr};

impl<'a> Checker<'a> {
    // -----------------------------------------------------------------------
    // From declared types
    // -----------------------------------------------------------------------

    pub(crate) fn shape_of_type(&self, ty: &TypeExpr) -> TypeShape {
        match ty {
            TypeExpr::Named { name, .. } => self.named_shape(name),
            TypeExpr::Pointer { to, .. } => TypeShape::Pointer(Box::new(self.shape_of_type(to))),
            TypeExpr::Slice { elem, .. } => TypeShape::Slice(Box::new(self.shape_of_type(elem))),
            TypeExpr::Array { elem, .. } => TypeShape::Array(Box::new(self.shape_of_type(elem))),
            TypeExpr::Map { key, value, .. } => TypeShape::Map(
                Box::new(self.shape_of_type(key)),
                Box::new(self.shape_of_type(value)),
            ),
            TypeExpr::Chan { elem, .. } => TypeShape::Chan(Box::new(self.shape_of_type(elem))),
            // option[T] carries T by value in a struct { v T; ok bool } — its
            // sendability IS the payload's sendability (option[int] crosses,
            // option[map] does not — the aliased map inside decides).
            TypeExpr::Option { elem, .. } => self.shape_of_type(elem),
            // fn-typed values are closures: captures make them unsendable at
            // boundaries (Tier 0 — the A5 perimeter).
            TypeExpr::Fn { .. } => TypeShape::Closure,
        }
    }

    fn named_shape(&self, name: &str) -> TypeShape {
        match name {
            "int" | "i8" | "int8" | "i16" | "int16" | "i32" | "int32" | "i64" | "int64" | "u8"
            | "uint8" | "u16" | "uint16" | "u32" | "uint32" | "u64" | "uint64" | "usize"
            | "isize" | "uintptr" | "float32" | "float64" | "f32" | "f64" | "bool" | "byte"
            | "rune" | "char" => TypeShape::Primitive,
            "string" => TypeShape::Str,
            _ => {
                if let Some(shape) = foreign::foreign_named_type(name) {
                    shape
                } else if self.structs.contains_key(name) {
                    TypeShape::Struct(Some(name.to_string()))
                } else {
                    TypeShape::Unknown
                }
            }
        }
    }

    /// Does this struct decl guard something with a `sync.*` lock? (Used for
    /// the contested-04 note: "Tier 0 does not credit locks at spawn sites".)
    pub(crate) fn struct_has_mutex_field(&self, sname: &str) -> bool {
        self.structs
            .get(sname)
            .map(|fields| {
                fields.iter().any(|(_, ty)| {
                    matches!(
                        self.shape_of_type(ty),
                        TypeShape::ForeignOpaque(ref t) if t.starts_with("sync.")
                    )
                })
            })
            .unwrap_or(false)
    }

    // -----------------------------------------------------------------------
    // From expressions
    // -----------------------------------------------------------------------

    pub(crate) fn shape_of_expr(&self, st: &FnState, expr: &Expr) -> TypeShape {
        match expr {
            Expr::Ident { name, .. } => self
                .lookup_binding(st, name)
                .map(|b| b.shape.clone())
                .unwrap_or(TypeShape::Unknown),
            Expr::Lit { kind, .. } => match kind {
                hy_syntax::LitKind::Int(_)
                | hy_syntax::LitKind::Float(_)
                | hy_syntax::LitKind::Bool(_)
                | hy_syntax::LitKind::Char(_) => TypeShape::Primitive,
                hy_syntax::LitKind::Str(_) | hy_syntax::LitKind::RawStr(_) => TypeShape::Str,
                hy_syntax::LitKind::Nil => TypeShape::Unknown,
            },
            Expr::Interp { .. } => TypeShape::Str,
            Expr::Binary { op, lhs, rhs, .. } => {
                // string concatenation stays a string (`const corpus = "a" + "b"`)
                if matches!(op, BinOp::Add)
                    && (self.shape_of_expr(st, lhs) == TypeShape::Str
                        || self.shape_of_expr(st, rhs) == TypeShape::Str)
                {
                    TypeShape::Str
                } else {
                    TypeShape::Primitive
                }
            }
            Expr::Unary { op, operand, .. } => match op {
                hy_syntax::UnOp::Addr => {
                    TypeShape::Pointer(Box::new(self.shape_of_expr(st, operand)))
                }
                _ => TypeShape::Primitive,
            },
            Expr::AddrOf { operand, .. } => {
                TypeShape::Pointer(Box::new(self.shape_of_expr(st, operand)))
            }
            Expr::Move { operand, .. }
            | Expr::Try { operand, .. }
            | Expr::Paren { inner: operand, .. } => self.shape_of_expr(st, operand),
            Expr::Receive { chan, .. } => match self.shape_of_expr(st, chan) {
                TypeShape::Chan(e) => *e,
                _ => TypeShape::Unknown,
            },
            Expr::Index { base, .. } => match self.shape_of_expr(st, base) {
                TypeShape::Map(_, v) => *v,
                TypeShape::Slice(e) | TypeShape::Array(e) => *e,
                _ => TypeShape::Unknown,
            },
            Expr::Slice { base, .. } => match self.shape_of_expr(st, base) {
                TypeShape::Slice(e) | TypeShape::Array(e) => TypeShape::Slice(e),
                TypeShape::Str => TypeShape::Str,
                _ => TypeShape::Unknown,
            },
            Expr::Field { base, name, .. } => {
                let base_shape = self.shape_of_expr(st, base);
                self.field_shape(&base_shape, name)
            }
            Expr::Call { callee, args, .. } => self.call_shape(st, callee, args),
            Expr::StructLit { ty, .. } => TypeShape::Struct(match ty {
                Some(TypeExpr::Named { name, .. }) => Some(name.clone()),
                _ => None,
            }),
            Expr::MapLit { key, value, .. } => TypeShape::Map(
                Box::new(self.shape_of_type(key)),
                Box::new(self.shape_of_type(value)),
            ),
            Expr::SliceLit { elem, items, .. } => TypeShape::Slice(Box::new(match elem {
                Some(t) => self.shape_of_type(t),
                None => items
                    .first()
                    .map(|i| self.shape_of_expr(st, i))
                    .unwrap_or(TypeShape::Unknown),
            })),
            // closures are unsendable values in Tier 0 (the A5 perimeter);
            // classify_value rejects FnLit literals before shape lookup —
            // this arm covers fn-typed bindings and fn-typed fields
            Expr::FnLit { .. } => TypeShape::Closure,
        }
    }

    /// Field type through (a pointer to) a declared struct.
    pub(crate) fn field_shape(&self, base: &TypeShape, field: &str) -> TypeShape {
        match base {
            TypeShape::Struct(Some(sname)) => self
                .structs
                .get(sname)
                .and_then(|fs| fs.iter().find(|(n, _)| n == field))
                .map(|(_, t)| self.shape_of_type(t))
                .unwrap_or(TypeShape::Unknown),
            TypeShape::Pointer(inner) => self.field_shape(inner, field),
            _ => TypeShape::Unknown,
        }
    }

    fn call_shape(&self, st: &FnState, callee: &Expr, args: &[CallArg]) -> TypeShape {
        match callee {
            Expr::Ident { name, .. } => match name.as_str() {
                // `make(chan T, n)` — defensive against parser spellings of
                // the type argument; defaults Unknown (fail-closed at
                // boundaries, O4.9). See the TECH DEBT note in foreign.rs.
                "make" => self.make_shape(args),
                "append" => args
                    .first()
                    .map(|a| self.shape_of_expr(st, &a.value))
                    .unwrap_or(TypeShape::Unknown),
                "len" | "cap" | "min" | "max" => TypeShape::Primitive,
                // `new(T)` is Go's `new`: it returns `*T` — a POINTER to
                // zeroed, mutable storage — never a primitive copy. Typing
                // it Primitive made it sendable-by-type (class 1), so
                // `p := new(S); task w(p)` shared a `*S` across tasks with no
                // diagnostic and raced (O4 class table: `*T` is a named
                // mutable GC value, not sendable; O4.9: unresolved/unknown
                // shapes fail closed). Type it as a pointer so it is
                // classified as shared mutable state and rejected at every
                // check-site. The pointee is inferred when the type argument
                // resolves; otherwise Unknown — still a non-sendable pointer.
                "new" => {
                    let pointee = match args.first().map(|a| &a.value) {
                        // `new(pool_stats)` — the argument is a type name,
                        // not a value; name a declared struct precisely.
                        Some(Expr::Ident { name, .. }) if self.structs.contains_key(name) => {
                            TypeShape::Struct(Some(name.clone()))
                        }
                        Some(other) => self.shape_of_expr(st, other),
                        None => TypeShape::Unknown,
                    };
                    TypeShape::Pointer(Box::new(pointee))
                }
                _ => self
                    .fns
                    .get(name.as_str())
                    .and_then(|f| f.results.first())
                    .map(|r| self.shape_of_type(&r.ty))
                    .unwrap_or(TypeShape::Unknown),
            },
            Expr::Field { base, name, .. } => {
                // package call (`serde_json.parse`) vs method call (`doc.array`)
                if let Expr::Ident { name: b, .. } = &**base {
                    if self.lookup_binding(st, b).is_none() && self.known_package(b) {
                        return foreign::package_result(b, name);
                    }
                }
                let recv = self.shape_of_expr(st, base);
                match receiver_type_name(&recv) {
                    Some(t) => foreign::method_result(&t, name),
                    None => TypeShape::Unknown,
                }
            }
            _ => TypeShape::Unknown,
        }
    }

    fn make_shape(&self, args: &[CallArg]) -> TypeShape {
        let Some(first) = args.first() else {
            return TypeShape::Unknown;
        };
        match &first.value {
            // The parser renders a type in expression position as a literal
            // node carrying the TypeExpr in `.ty` (`make(chan bool, n)` →
            // StructLit{ty: Chan}); other spellings degrade to Unknown.
            Expr::StructLit { ty: Some(t), .. } => self.shape_of_type(t),
            Expr::SliceLit { elem: Some(_), .. } => TypeShape::Slice(Box::new(TypeShape::Unknown)),
            Expr::MapLit { .. } => {
                TypeShape::Map(Box::new(TypeShape::Unknown), Box::new(TypeShape::Unknown))
            }
            _ => TypeShape::Unknown,
        }
    }

    pub(crate) fn known_package(&self, pkg: &str) -> bool {
        self.packages.contains(pkg) || foreign::BUILTIN_PACKAGES.contains(&pkg)
    }

    // -----------------------------------------------------------------------
    // Loop variables
    // -----------------------------------------------------------------------

    /// Shapes of the variables bound by `for v[, i] in <expr>`.
    pub(crate) fn iterate_var_shapes(
        &self,
        st: &FnState,
        expr: &Expr,
        n_vars: usize,
    ) -> Vec<TypeShape> {
        let s = self.shape_of_expr(st, expr);
        let one = |v: TypeShape| {
            if n_vars >= 2 {
                vec![TypeShape::Primitive, v]
            } else {
                vec![v]
            }
        };
        match &s {
            // iterating a view yields views (element loans, corpus 07/11/12)
            TypeShape::BorrowHandle(_) => vec![s.clone()],
            TypeShape::Slice(e) | TypeShape::Array(e) | TypeShape::Chan(e) => one((**e).clone()),
            TypeShape::Map(k, v) => {
                if n_vars >= 2 {
                    vec![(**k).clone(), (**v).clone()]
                } else {
                    vec![(**v).clone()]
                }
            }
            _ => vec![TypeShape::Unknown; n_vars.max(1)],
        }
    }

    // -----------------------------------------------------------------------
    // Source types for diagnostics
    // -----------------------------------------------------------------------

    /// The as-written type of an initializer, when directly available
    /// (literals, aliases, local-fn results). `None` = use the shape render.
    pub(crate) fn ty_of_expr(&self, st: &FnState, expr: &Expr) -> Option<TypeExpr> {
        match expr {
            Expr::Ident { name, .. } => self.lookup_binding(st, name).and_then(|b| b.ty.clone()),
            Expr::StructLit { ty, .. } => ty.clone(),
            Expr::MapLit {
                key, value, span, ..
            } => Some(TypeExpr::Map {
                key: key.clone(),
                value: value.clone(),
                span: *span,
            }),
            Expr::SliceLit {
                elem: Some(e),
                span,
                ..
            } => Some(TypeExpr::Slice {
                elem: e.clone(),
                span: *span,
            }),
            Expr::Move { operand, .. }
            | Expr::Try { operand, .. }
            | Expr::Paren { inner: operand, .. } => self.ty_of_expr(st, operand),
            Expr::Call { callee, .. } => match callee.as_ref() {
                Expr::Ident { name, .. } => self
                    .fns
                    .get(name.as_str())
                    .and_then(|f| f.results.first())
                    .map(|r| r.ty.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Shapes for a multi-name define or assign from one value (`v, ok := m[k]`,
    /// `v, ok := <-ch`, `a, b := f()`).
    pub(crate) fn multi_value_shapes(
        &self,
        st: &FnState,
        value: &Expr,
        n_names: usize,
    ) -> Vec<TypeShape> {
        let val = crate::model::unwrap_parens(value);
        if n_names == 2 {
            if let Expr::Index { base, .. } = val {
                if let TypeShape::Map(_, v) = self.shape_of_expr(st, base) {
                    return vec![*v, TypeShape::Primitive]; // v, ok := m[k]
                }
            }
            // `v, ok := <-ch` — the value is the channel's element; `ok` is
            // the receive-ok flag (a bool)
            if let Expr::Receive { chan, .. } = val {
                let elem = match self.shape_of_expr(st, chan) {
                    TypeShape::Chan(e) => *e,
                    _ => TypeShape::Unknown,
                };
                return vec![elem, TypeShape::Primitive];
            }
        }
        if let Expr::Call { callee, .. } = val {
            if let Expr::Ident { name, .. } = crate::model::unwrap_parens(callee) {
                if self.lookup_binding(st, name).is_none() {
                    if let Some(f) = self.fns.get(name.as_str()) {
                        if f.results.len() == n_names {
                            return f
                                .results
                                .iter()
                                .map(|r| self.shape_of_type(&r.ty))
                                .collect();
                        }
                    }
                }
            }
        }
        vec![TypeShape::Unknown; n_names]
    }

    /// Declared result types for a multi-name define or assign from a single
    /// call expression (`a, b := f()`), when statically resolvable.
    pub(crate) fn multi_value_tys(
        &self,
        st: &FnState,
        value: &Expr,
        n_names: usize,
    ) -> Vec<Option<TypeExpr>> {
        let val = crate::model::unwrap_parens(value);
        if let Expr::Call { callee, .. } = val {
            if let Expr::Ident { name, .. } = crate::model::unwrap_parens(callee) {
                if self.lookup_binding(st, name).is_none() {
                    if let Some(f) = self.fns.get(name.as_str()) {
                        if f.results.len() == n_names {
                            return f.results.iter().map(|r| Some(r.ty.clone())).collect();
                        }
                    }
                }
            }
        }
        vec![None; n_names]
    }
}

/// The boundary type name that keys the method-mode table for a receiver
/// shape ("serde_json.value", "atomic", ...).
pub(crate) fn receiver_type_name(shape: &TypeShape) -> Option<String> {
    match shape {
        TypeShape::OwnHandle(t) | TypeShape::BorrowHandle(t) | TypeShape::ForeignOpaque(t) => {
            Some(t.clone())
        }
        TypeShape::Atomic => Some("atomic.int".to_string()),
        TypeShape::Pointer(inner) if matches!(**inner, TypeShape::Atomic) => {
            Some("atomic.int".to_string())
        }
        _ => None,
    }
}
