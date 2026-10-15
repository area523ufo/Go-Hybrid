//! arith.rs — constant arithmetic that would make emitted Go unbuildable.
//!
//! Issue #149: `x / 0` and `x % 0` with a literal `0` divisor pass
//! `hyb check` (0 diagnostics) and then fail `go vet` /
//! `go build` with `invalid operation: division by zero`. The accepted-
//! should-emit-buildable-Go contract requires a checker diagnostic
//! (HYB-E6001) for that narrow literal case. Non-constant zero divisors
//! stay out of scope — Go accepts them and panics at run time.

use crate::model::{unwrap_parens, Binding, Checker, FnState, TypeShape};
use hy_diag::{Diagnostic, Span};
use hy_syntax::{
    AssignOp, BinOp, Block, Decl, Expr, ForKind, InterpPart, LitKind, LocalKind, Place, PlaceKind,
    SelectArmKind, Stmt, TypeExpr,
};
use std::collections::HashMap;

impl<'a> Checker<'a> {
    /// File-level structural validity checks (#201):
    ///   * C1–C4: redeclarations of top-level functions, file-level consts,
    ///     struct fields, and methods on the same receiver base type.
    ///   * D1–D2: invalid method receiver types (built-in/non-local types,
    ///     pointer-to-pointer `**T`, or composite non-named types).
    ///   * E1–E2: invalid array bounds in top-level declarations and fn
    ///     signatures.
    ///   * A / B4 / #149 inside file-level `const` initializers.
    pub(crate) fn check_file_decls(&mut self) {
        let decls = self.file.decls.clone();
        let mut seen_fns: HashMap<String, Span> = HashMap::new();
        let mut seen_consts: HashMap<String, Span> = HashMap::new();
        let mut seen_types: HashMap<String, Span> = HashMap::new();
        let mut seen_methods: HashMap<(String, String), Span> = HashMap::new();

        for d in &decls {
            match d {
                Decl::Import { .. } => {}
                Decl::Const(c) => {
                    if c.name != "_" {
                        if let Some(prev) = seen_consts.insert(c.name.clone(), c.span) {
                            self.emit_redeclared(
                                c.span,
                                "constant",
                                &c.name,
                                prev,
                            );
                        } else if let Some(prev) = seen_fns.get(&c.name).copied() {
                            self.emit_redeclared(
                                c.span,
                                "identifier",
                                &c.name,
                                prev,
                            );
                        }
                    }
                    if let Some(ty) = &c.ty {
                        self.check_type_expr(None, ty);
                    }
                    self.check_expr_const_zero_divisor(None, &c.value);
                }
                Decl::Struct(s) => {
                    if s.name != "_" {
                        if let Some(prev) = seen_types.insert(s.name.clone(), s.span) {
                            self.emit_redeclared(s.span, "type", &s.name, prev);
                        }
                    }
                    let mut seen_fields: HashMap<String, Span> = HashMap::new();
                    for field in &s.fields {
                        if field.name != "_" {
                            if let Some(prev) = seen_fields.insert(field.name.clone(), field.span) {
                                let msg = format!(
                                    "duplicate field `{}` in struct `{}` (previously declared at {}:{}) (HYB-E2001)",
                                    field.name, s.name, prev.start.line, prev.start.col
                                );
                                self.diags.push(
                                    Diagnostic::error("HYB-E2001", self.path.clone(), field.span, msg)
                                        .with_notes(vec![
                                            format!(
                                                "why: Go rejects structs with duplicate field names (`{}.{}` redeclared), so the emitted Go would fail to compile (issue #201)",
                                                s.name, field.name
                                            ),
                                            format!(
                                                "fix: rename or remove the duplicate field `{}` in `struct {}`",
                                                field.name, s.name
                                            ),
                                        ]),
                                );
                            }
                        }
                        self.check_type_expr(None, &field.ty);
                    }
                }
                Decl::Enum(e) => {
                    if e.name != "_" {
                        if let Some(prev) = seen_types.insert(e.name.clone(), e.span) {
                            self.emit_redeclared(e.span, "type", &e.name, prev);
                        }
                    }
                    for v in &e.variants {
                        if let Some(t) = &v.payload {
                            self.check_type_expr(None, t);
                        }
                    }
                }
                Decl::TypeAlias(ta) => {
                    if ta.name != "_" {
                        if let Some(prev) = seen_types.insert(ta.name.clone(), ta.span) {
                            self.emit_redeclared(ta.span, "type", &ta.name, prev);
                        }
                    }
                    self.check_type_expr(None, &ta.ty);
                }
                Decl::Fn(f) => {
                    if let Some(r) = &f.receiver {
                        self.check_method_receiver(&f.name, r, f.span, &mut seen_methods);
                        self.check_type_expr(None, &r.ty);
                    } else if f.name != "_" {
                        if let Some(prev) = seen_fns.insert(f.name.clone(), f.span) {
                            self.emit_redeclared(
                                f.span,
                                "function",
                                &f.name,
                                prev,
                            );
                        } else if let Some(prev) = seen_consts.get(&f.name).copied() {
                            self.emit_redeclared(
                                f.span,
                                "identifier",
                                &f.name,
                                prev,
                            );
                        }
                    }
                    for p in &f.params {
                        self.check_type_expr(None, &p.ty);
                    }
                    for res in &f.results {
                        self.check_type_expr(None, &res.ty);
                    }
                    if let Some(body) = &f.body {
                        self.check_block_const_redecls(body);
                    }
                }
            }
        }
    }

    fn emit_redeclared(&mut self, span: Span, kind: &str, name: &str, prev: Span) {
        let msg = format!(
            "`{}` redeclared in this block — {} `{}` was previously declared at {}:{} (HYB-E2001)",
            name, kind, name, prev.start.line, prev.start.col
        );
        self.diags.push(
            Diagnostic::error("HYB-E2001", self.path.clone(), span, msg).with_notes(vec![
                format!(
                    "why: Go rejects duplicate declarations of `{}` in the same package/block (`{} redeclared in this block`), so an accepted Hybrid file would emit unbuildable Go (issue #201)",
                    name, name
                ),
                format!(
                    "fix: rename one of the `{}` declarations or remove the duplicate",
                    name
                ),
            ]),
        );
    }

    fn check_block_const_redecls(&mut self, block: &Block) {
        let mut seen_consts: HashMap<String, Span> = HashMap::new();
        for stmt in &block.stmts {
            match stmt {
                Stmt::Local(l) if l.kind == LocalKind::Const => {
                    for name in &l.names {
                        if name != "_" {
                            if let Some(prev) = seen_consts.insert(name.clone(), l.span) {
                                self.emit_redeclared(l.span, "constant", name, prev);
                            }
                        }
                    }
                }
                Stmt::If {
                    then, otherwise, ..
                } => {
                    self.check_block_const_redecls(then);
                    if let Some(other) = otherwise {
                        self.check_stmt_const_redecls(other);
                    }
                }
                Stmt::For { body, .. } | Stmt::Managed { body, .. } => {
                    self.check_block_const_redecls(body);
                }
                Stmt::Block { block: b, .. } => {
                    self.check_block_const_redecls(b);
                }
                Stmt::Match { arms, .. } => {
                    for arm in arms {
                        self.check_block_const_redecls(&arm.body);
                    }
                }
                Stmt::Select { arms, .. } => {
                    for arm in arms {
                        self.check_block_const_redecls(&arm.body);
                    }
                }
                _ => {}
            }
        }
    }

    fn check_stmt_const_redecls(&mut self, stmt: &Stmt) {
        if let Stmt::If {
            then, otherwise, ..
        } = stmt
        {
            self.check_block_const_redecls(then);
            if let Some(other) = otherwise {
                self.check_stmt_const_redecls(other);
            }
        } else if let Stmt::Block { block, .. } = stmt {
            self.check_block_const_redecls(block);
        }
    }

    fn is_declared_receiver_type(&self, base: &str) -> bool {
        self.file.decls.iter().any(|d| match d {
            Decl::Struct(s) => s.name == base,
            Decl::Enum(e) => e.name == base,
            _ => false,
        })
    }

    fn check_method_receiver(
        &mut self,
        fn_name: &str,
        r: &hy_syntax::Receiver,
        fn_span: Span,
        seen_methods: &mut HashMap<(String, String), Span>,
    ) {
        match &r.ty {
            TypeExpr::Pointer { span, .. } => {
                let rendered = if r.is_pointer {
                    format!("*{}", r.ty.render())
                } else {
                    r.ty.render()
                };
                let msg = format!(
                    "invalid receiver type `{}` on method `{}` (`{}` is a pointer type) (HYB-E2001)",
                    rendered, fn_name, rendered
                );
                self.diags.push(
                    Diagnostic::error("HYB-E2001", self.path.clone(), *span, msg).with_notes(vec![
                        "why: Go forbids pointer-to-pointer method receivers (`invalid receiver type **T (**T is a pointer type)`); a method receiver must be `T` or `*T` where `T` is a locally declared struct (issue #201)".to_string(),
                        "fix: change the receiver type from `**T` to `*T` or `T`".to_string(),
                    ]),
                );
            }
            TypeExpr::Named { name, span } => {
                let base = name.split('[').next().unwrap_or(name);
                if !self.is_declared_receiver_type(base) {
                    let msg = format!(
                        "cannot define method `{}` on non-local or built-in type `{}` (HYB-E2001)",
                        fn_name, name
                    );
                    self.diags.push(
                        Diagnostic::error("HYB-E2001", self.path.clone(), *span, msg).with_notes(
                            vec![
                                format!(
                                    "why: Go only allows methods on locally defined types in the same package (`cannot define new methods on non-local type {}`), not on built-ins like `int`/`string` or type aliases (issue #201)",
                                    name
                                ),
                                format!(
                                    "fix: wrap `{}` in a `struct` declared in this file, or write `{}` as a plain function taking `{}` as a parameter",
                                    name, fn_name, name
                                ),
                            ],
                        ),
                    );
                    return;
                }
                if fn_name != "_" {
                    let key = (base.to_string(), fn_name.to_string());
                    if let Some(prev) = seen_methods.insert(key, fn_span) {
                        let msg = format!(
                            "method `{}.{}` already declared at {}:{} (HYB-E2001)",
                            base, fn_name, prev.start.line, prev.start.col
                        );
                        self.diags.push(
                            Diagnostic::error("HYB-E2001", self.path.clone(), fn_span, msg)
                                .with_notes(vec![
                                    format!(
                                        "why: Go rejects duplicate method declarations on the same receiver type (`{}.{} redeclared in this block`) (issue #201)",
                                        base, fn_name
                                    ),
                                    format!(
                                        "fix: rename one of the `{}` methods on `{}` or remove the duplicate",
                                        fn_name, base
                                    ),
                                ]),
                        );
                    }
                }
            }
            other => {
                let span = other.span();
                let msg = format!(
                    "invalid receiver type `{}` on method `{}` (HYB-E2001)",
                    other.render(),
                    fn_name
                );
                self.diags.push(
                    Diagnostic::error("HYB-E2001", self.path.clone(), span, msg).with_notes(vec![
                        "why: Go method receivers must be a locally declared `struct` (or `*struct`), not a slice, map, channel, array, or function type (issue #201)".to_string(),
                        "fix: declare a named `struct` for the receiver or use a regular function".to_string(),
                    ]),
                );
            }
        }
    }

    /// Validate `TypeExpr::Array` lengths (Sub-family E: negative constant
    /// length `[-1]T` or non-constant length `[n]T`).
    pub(crate) fn check_type_expr(&mut self, st: Option<&FnState>, ty: &TypeExpr) {
        match ty {
            TypeExpr::Named { .. } => {}
            TypeExpr::Pointer { to, .. }
            | TypeExpr::Slice { elem: to, .. }
            | TypeExpr::Chan { elem: to, .. }
            | TypeExpr::Option { elem: to, .. } => self.check_type_expr(st, to),
            TypeExpr::Map { key, value, .. } => {
                self.check_type_expr(st, key);
                self.check_type_expr(st, value);
            }
            TypeExpr::Fn {
                params, results, ..
            } => {
                for p in params {
                    self.check_type_expr(st, &p.ty);
                }
                for r in results {
                    self.check_type_expr(st, r);
                }
            }
            TypeExpr::Array { len, elem, span } => {
                if let Some(len_expr) = len {
                    match self.eval_const_int(st, len_expr, 0) {
                        Some(v) if v < 0 => {
                            let msg = format!(
                                "invalid array length `{}` (value `{}`) in `{}` — array bound must be non-negative (HYB-E6002)",
                                len_expr.render(),
                                v,
                                ty.render()
                            );
                            self.diags.push(
                                Diagnostic::error("HYB-E6002", self.path.clone(), *span, msg)
                                    .with_notes(vec![
                                        "why: Go rejects negative array bounds at compile time (`invalid array length`), so the emitted Go would not build (issue #201)".to_string(),
                                        "fix: use a non-negative integer constant for the array length, or use a slice `[]T`".to_string(),
                                    ]),
                            );
                        }
                        Some(_) => {}
                        None => {
                            let msg = format!(
                                "non-constant array bound `{}` in `{}` — array length must be a compile-time integer constant (HYB-E2001)",
                                len_expr.render(),
                                ty.render()
                            );
                            self.diags.push(
                                Diagnostic::error("HYB-E2001", self.path.clone(), *span, msg)
                                    .with_notes(vec![
                                        "why: Go requires `[N]T` array lengths to be compile-time integer constants (`non-constant array bound`); runtime bindings (`:=`, `var`, `let`, parameters) cannot size a fixed array (issue #201)".to_string(),
                                        format!(
                                            "fix: declare `{}` as `const` if it is a compile-time constant, or use `[]{}` (`make([]{}, {})`) for a runtime-sized slice",
                                            len_expr.render(),
                                            elem.render(),
                                            elem.render(),
                                            len_expr.render()
                                        ),
                                    ]),
                            );
                        }
                    }
                }
                self.check_type_expr(st, elem);
            }
        }
    }

    /// Pass-B entry: walk the same expression surface as `walk::own_uses`.
    /// Nested block bodies are NOT recursed here — `walk::flatten` already
    /// lists those statements, and a second walk would duplicate diagnostics.
    pub(crate) fn check_stmt_const_zero_divisor(&mut self, st: &FnState, stmt: &Stmt) {
        let mut st_cow: Option<FnState> = None;
        self.check_stmt_const_zero_divisor_inner(Some(st), &mut st_cow, stmt, /*deep=*/ false);
    }

    fn check_stmt_const_zero_divisor_inner(
        &mut self,
        base_st: Option<&FnState>,
        deep_st: &mut Option<FnState>,
        stmt: &Stmt,
        deep: bool,
    ) {
        let cur_st: Option<&FnState> = deep_st.as_ref().or(base_st);
        match stmt {
            Stmt::Local(l) => {
                if let Some(ty) = &l.ty {
                    self.check_type_expr(cur_st, ty);
                    if deep {
                        for (name, val) in l.names.iter().zip(l.values.iter()) {
                            self.check_const_overflow_init(name, ty, val);
                        }
                    }
                }
                for v in &l.values {
                    let cur_st = deep_st.as_ref().or(base_st);
                    self.check_expr_const_zero_divisor(cur_st, v);
                }
                if deep {
                    if let Some( dst ) = deep_st.as_mut() {
                        let immutable = matches!(l.kind, LocalKind::Const);
                        if l.values.is_empty() {
                            let shape = l
                                .ty
                                .as_ref()
                                .map(|t| self.shape_of_type(t))
                                .unwrap_or(TypeShape::Unknown);
                            for name in &l.names {
                                dst.env_define(
                                    name,
                                    Binding {
                                        shape: shape.clone(),
                                        ty: l.ty.clone(),
                                        immutable,
                                        managed_taint: false,
                                        moved: None,
                                        non_owned_origin: None,
                                    },
                                );
                            }
                        } else {
                            for (name, val) in l.names.iter().zip(l.values.iter()) {
                                let shape = match &l.ty {
                                    Some(t) => self.shape_of_type(t),
                                    None => self.shape_of_expr(dst, val),
                                };
                                dst.env_define(
                                    name,
                                    Binding {
                                        shape,
                                        ty: l.ty.clone(),
                                        immutable,
                                        managed_taint: false,
                                        moved: None,
                                        non_owned_origin: None,
                                    },
                                );
                            }
                        }
                    }
                }
            }
            Stmt::Assign {
                targets,
                op,
                values,
                span,
            } => {
                for t in targets {
                    let cur_st = deep_st.as_ref().or(base_st);
                    self.check_place_const_zero_divisor(cur_st, t);
                }
                for v in values {
                    let cur_st = deep_st.as_ref().or(base_st);
                    self.check_expr_const_zero_divisor(cur_st, v);
                }
                if matches!(op, AssignOp::DivAssign | AssignOp::ModAssign)
                    && values.len() == 1
                    && is_int_literal_zero(&values[0])
                {
                    self.emit_const_zero_divisor(*span, assign_op_txt(*op));
                }
                let cur_st = deep_st.as_ref().or(base_st);
                if matches!(op, AssignOp::ShlAssign | AssignOp::ShrAssign) && values.len() == 1 {
                    if let Some(v) = self.eval_const_int(cur_st, &values[0], 0) {
                        if v < 0 {
                            self.emit_negative_shift(*span, &values[0], v);
                        }
                    }
                }
            }
            Stmt::Expr { expr, .. } => self.check_expr_const_zero_divisor(cur_st, expr),
            Stmt::Send { chan, value, .. } => {
                self.check_expr_const_zero_divisor(cur_st, chan);
                let cur_st = deep_st.as_ref().or(base_st);
                self.check_expr_const_zero_divisor(cur_st, value);
            }
            Stmt::If {
                init,
                cond,
                then,
                otherwise,
                ..
            } => {
                if deep {
                    if let Some(init) = init {
                        self.check_stmt_const_zero_divisor_inner(base_st, deep_st, init, true);
                    }
                }
                let cur_st = deep_st.as_ref().or(base_st);
                self.check_expr_const_zero_divisor(cur_st, cond);
                if deep {
                    for s in &then.stmts {
                        self.check_stmt_const_zero_divisor_inner(base_st, deep_st, s, true);
                    }
                    if let Some(other) = otherwise {
                        self.check_stmt_const_zero_divisor_inner(base_st, deep_st, other, true);
                    }
                }
            }
            Stmt::For { kind, body, .. } => {
                match kind {
                    ForKind::While { cond } => self.check_expr_const_zero_divisor(cur_st, cond),
                    ForKind::Range { lo, hi, .. } => {
                        self.check_expr_const_zero_divisor(cur_st, lo);
                        let cur_st = deep_st.as_ref().or(base_st);
                        self.check_expr_const_zero_divisor(cur_st, hi);
                    }
                    ForKind::Iterate { expr, .. } => {
                        self.check_expr_const_zero_divisor(cur_st, expr)
                    }
                    ForKind::Infinite => {}
                }
                if deep {
                    for s in &body.stmts {
                        self.check_stmt_const_zero_divisor_inner(base_st, deep_st, s, true);
                    }
                }
            }
            Stmt::Return { values, .. } => {
                for v in values {
                    let cur_st = deep_st.as_ref().or(base_st);
                    self.check_expr_const_zero_divisor(cur_st, v);
                }
            }
            Stmt::Task { callee, args, .. } => {
                self.check_expr_const_zero_divisor(cur_st, callee);
                for a in args {
                    let cur_st = deep_st.as_ref().or(base_st);
                    self.check_expr_const_zero_divisor(cur_st, &a.value);
                }
            }
            Stmt::Managed { body, .. } => {
                if deep {
                    for s in &body.stmts {
                        self.check_stmt_const_zero_divisor_inner(base_st, deep_st, s, true);
                    }
                }
            }
            Stmt::Match { subject, arms, .. } => {
                self.check_expr_const_zero_divisor(cur_st, subject);
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        let cur_st = deep_st.as_ref().or(base_st);
                        self.check_expr_const_zero_divisor(cur_st, g);
                    }
                    if deep {
                        for s in &arm.body.stmts {
                            self.check_stmt_const_zero_divisor_inner(base_st, deep_st, s, true);
                        }
                    }
                }
            }
            Stmt::Defer { call, .. } => self.check_expr_const_zero_divisor(cur_st, call),
            Stmt::Break { .. } | Stmt::Continue { .. } => {}
            Stmt::Block { block, .. } => {
                if deep {
                    for s in &block.stmts {
                        self.check_stmt_const_zero_divisor_inner(base_st, deep_st, s, true);
                    }
                }
            }
            Stmt::Select { arms, .. } => {
                for arm in arms {
                    match &arm.kind {
                        SelectArmKind::Send { chan, value } => {
                            let cur_st = deep_st.as_ref().or(base_st);
                            self.check_expr_const_zero_divisor(cur_st, chan);
                            let cur_st = deep_st.as_ref().or(base_st);
                            self.check_expr_const_zero_divisor(cur_st, value);
                        }
                        SelectArmKind::Recv { chan, .. } => {
                            let cur_st = deep_st.as_ref().or(base_st);
                            self.check_expr_const_zero_divisor(cur_st, chan)
                        }
                        SelectArmKind::Default => {}
                    }
                    if deep {
                        for s in &arm.body.stmts {
                            self.check_stmt_const_zero_divisor_inner(base_st, deep_st, s, true);
                        }
                    }
                }
            }
        }
    }

    fn check_place_const_zero_divisor(&mut self, st: Option<&FnState>, place: &Place) {
        match &place.kind {
            PlaceKind::Ident(_) => {}
            PlaceKind::Index { base, index } => {
                self.check_place_const_zero_divisor(st, base);
                self.check_expr_const_zero_divisor(st, index);
            }
            PlaceKind::Field { base, .. } | PlaceKind::AddrOf { base } => {
                self.check_place_const_zero_divisor(st, base)
            }
        }
    }

    pub(crate) fn check_expr_const_zero_divisor(&mut self, st: Option<&FnState>, expr: &Expr) {
        match expr {
            Expr::Binary { op, lhs, rhs, span } => {
                self.check_expr_const_zero_divisor(st, lhs);
                self.check_expr_const_zero_divisor(st, rhs);
                if matches!(op, BinOp::Div | BinOp::Mod) && is_int_literal_zero(rhs) {
                    self.emit_const_zero_divisor(*span, bin_op_txt(*op));
                }
                if matches!(op, BinOp::Shl | BinOp::Shr) {
                    if let Some(v) = self.eval_const_int(st, rhs, 0) {
                        if v < 0 {
                            self.emit_negative_shift(*span, rhs, v);
                        }
                    }
                }
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    self.check_equality_comparability(st, *op, lhs, rhs, *span);
                }
            }
            Expr::Unary { operand, .. }
            | Expr::AddrOf { operand, .. }
            | Expr::Move { operand, .. }
            | Expr::Try { operand, .. }
            | Expr::Paren { inner: operand, .. }
            | Expr::Field { base: operand, .. }
            | Expr::Receive { chan: operand, .. } => {
                self.check_expr_const_zero_divisor(st, operand)
            }
            Expr::Index { base, index, .. } => {
                self.check_expr_const_zero_divisor(st, base);
                self.check_expr_const_zero_divisor(st, index);
            }
            Expr::Slice { base, lo, hi, .. } => {
                self.check_expr_const_zero_divisor(st, base);
                if let Some(lo) = lo {
                    self.check_expr_const_zero_divisor(st, lo);
                }
                if let Some(hi) = hi {
                    self.check_expr_const_zero_divisor(st, hi);
                }
            }
            Expr::Call { callee, args, .. } => {
                self.check_expr_const_zero_divisor(st, callee);
                for a in args {
                    self.check_expr_const_zero_divisor(st, &a.value);
                }
            }
            Expr::StructLit { ty, fields, .. } => {
                if let Some(t) = ty {
                    self.check_type_expr(st, t);
                }
                for f in fields {
                    self.check_expr_const_zero_divisor(st, &f.value);
                }
            }
            Expr::SliceLit { elem, items, .. } => {
                if let Some(t) = elem {
                    self.check_type_expr(st, t);
                }
                for i in items {
                    self.check_expr_const_zero_divisor(st, i);
                }
            }
            Expr::MapLit {
                key,
                value,
                entries,
                ..
            } => {
                self.check_type_expr(st, key);
                self.check_type_expr(st, value);
                for (k, v) in entries {
                    self.check_expr_const_zero_divisor(st, k);
                    self.check_expr_const_zero_divisor(st, v);
                }
            }
            Expr::Interp { parts, .. } => {
                for p in parts {
                    if let InterpPart::Expr(e) = p {
                        self.check_expr_const_zero_divisor(st, e);
                    }
                }
            }
            Expr::FnLit {
                params,
                results,
                body,
                ..
            } => {
                for p in params {
                    self.check_type_expr(st, &p.ty);
                }
                for r in results {
                    self.check_type_expr(st, &r.ty);
                }
                let mut child_st = st.cloned().unwrap_or_default();
                child_st.scope_push();
                for p in params {
                    let shape = self.shape_of_type(&p.ty);
                    child_st.env_define(
                        &p.name,
                        Binding {
                            shape,
                            ty: Some(p.ty.clone()),
                            immutable: false,
                            managed_taint: false,
                            moved: None,
                            non_owned_origin: None,
                        },
                    );
                }
                let mut deep_st = Some(child_st);
                // Closure bodies are not flattened into Pass B — deep-walk.
                for stmt in &body.stmts {
                    self.check_stmt_const_zero_divisor_inner(None, &mut deep_st, stmt, /*deep=*/ true);
                }
            }
            Expr::Ident { .. } | Expr::Lit { .. } => {}
        }
    }

    fn emit_negative_shift(&mut self, span: Span, rhs: &Expr, v: i128) {
        let msg = format!(
            "negative shift count `{}` (value `{}`) — Go rejects negative shift counts at compile time (HYB-E6002)",
            rhs.render(),
            v
        );
        self.diags.push(
            Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(vec![
                "why: a negative constant shift count is a Go compile error (`invalid operation: negative shift count`); accepted Hybrid programs must emit buildable Go (issue #201)".to_string(),
                "fix: use a non-negative shift count".to_string(),
            ]),
        );
    }

    fn check_equality_comparability(
        &mut self,
        st: Option<&FnState>,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
    ) {
        if Self::is_nil_literal(unwrap_parens(lhs)) || Self::is_nil_literal(unwrap_parens(rhs)) {
            return;
        }
        let reason = self
            .incomparable_expr_reason(st, lhs)
            .or_else(|| self.incomparable_expr_reason(st, rhs));
        let Some(reason) = reason else {
            return;
        };
        let msg = format!(
            "invalid operation `{} {} {}`: operator `{}` is not defined on {} (HYB-E2001)",
            lhs.render(),
            op.render(),
            rhs.render(),
            op.render(),
            reason
        );
        self.diags.push(
            Diagnostic::error("HYB-E2001", self.path.clone(), span, msg).with_notes(vec![
                "why: Go forbids `==` and `!=` on maps, slices, functions/closures (except comparison to `nil`), and on structs or arrays containing those types (`invalid operation: … cannot be compared`), so the emitted Go would fail to build (issue #201)".to_string(),
                "fix: compare element-by-element in a loop, compare lengths/keys, or compare a comparable field".to_string(),
            ]),
        );
    }

    fn incomparable_expr_reason(&self, st: Option<&FnState>, expr: &Expr) -> Option<String> {
        let e = unwrap_parens(expr);
        if let Expr::Ident { name, .. } = e {
            let bound = match st {
                Some(s) => self.lookup_binding(s, name),
                None => self.consts.get(name),
            };
            if bound.is_none() && self.fns.contains_key(name.as_str()) {
                return Some(format!(
                    "function `{}` (functions can only be compared to `nil`)",
                    name
                ));
            }
        }
        let empty = FnState::default();
        let shape = self.shape_of_expr(st.unwrap_or(&empty), e);
        self.shape_incomparable_reason(&shape, 0)
    }

    fn shape_incomparable_reason(&self, shape: &TypeShape, depth: usize) -> Option<String> {
        if depth > 16 {
            return None;
        }
        match shape {
            TypeShape::Map(_, _) => Some("map (maps can only be compared to `nil`)".to_string()),
            TypeShape::Slice(_) => Some("slice (slices can only be compared to `nil`)".to_string()),
            TypeShape::Closure => {
                Some("function/closure (functions can only be compared to `nil`)".to_string())
            }
            TypeShape::Array(elem) => self
                .shape_incomparable_reason(elem, depth + 1)
                .map(|r| format!("array containing incomparable {}", r)),
            TypeShape::Struct(Some(sname)) => {
                let base = sname.split('[').next().unwrap_or(sname);
                if let Some(fields) = self.structs.get(base) {
                    for (fname, fty) in fields {
                        let fshape = self.shape_of_type(fty);
                        if let Some(r) = self.shape_incomparable_reason(&fshape, depth + 1) {
                            return Some(format!(
                                "struct `{}` containing incomparable field `{}` ({})",
                                sname, fname, r
                            ));
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn emit_const_zero_divisor(&mut self, span: Span, op_txt: &str) {
        let msg = format!(
            "division by constant zero (`{}`): Go rejects this at compile time, so the emitted module would not build",
            op_txt
        );
        self.diags.push(
            Diagnostic::error("HYB-E6001", self.path.clone(), span, msg).with_notes(vec![
                "why: a literal `0` divisor is a Go compile error (`invalid operation: division by zero`); Hybrid's accepted programs must emit buildable Go (issue #149)".to_string(),
                "fix: use a non-zero constant, or bind the divisor to a variable if a run-time panic is the intended behaviour".to_string(),
            ]),
        );
    }
}

fn bin_op_txt(op: BinOp) -> &'static str {
    match op {
        BinOp::Div => "/",
        BinOp::Mod => "%",
        _ => "?",
    }
}

fn assign_op_txt(op: AssignOp) -> &'static str {
    match op {
        AssignOp::DivAssign => "/=",
        AssignOp::ModAssign => "%=",
        _ => "?",
    }
}

fn is_int_literal_zero(expr: &Expr) -> bool {
    match unwrap_parens(expr) {
        Expr::Lit {
            kind: LitKind::Int(raw),
            ..
        } => int_lit_is_zero(raw),
        _ => false,
    }
}

fn int_lit_is_zero(raw: &str) -> bool {
    let s: String = raw.chars().filter(|c| *c != '_').collect();
    if s.is_empty() {
        return false;
    }
    let (radix, digits) = if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
    {
        (16, rest)
    } else if let Some(rest) = s.strip_prefix("0o").or_else(|| s.strip_prefix("0O")) {
        (8, rest)
    } else if let Some(rest) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
        (2, rest)
    } else {
        (10, s.as_str())
    };
    if digits.is_empty() {
        return false;
    }
    u128::from_str_radix(digits, radix)
        .map(|v| v == 0)
        .unwrap_or(false)
}

#[cfg(test)]
mod lit_zero_tests {
    use super::int_lit_is_zero;

    #[test]
    fn recognizes_zero_spellings() {
        for s in ["0", "00", "0_0", "0x0", "0X00", "0o0", "0b0", "0b000"] {
            assert!(int_lit_is_zero(s), "{s}");
        }
    }

    #[test]
    fn rejects_nonzero() {
        for s in ["1", "10", "0x1", "0b1", "0o7", "00_1"] {
            assert!(!int_lit_is_zero(s), "{s}");
        }
    }
}
