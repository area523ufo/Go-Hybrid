//! const_overflow.rs — constant initializers that overflow a declared
//! fixed-width integer type (issue #148).
//!
//! `var n int8 = 300` (and the file-level `const` twin) pass `hyb check`
//! with 0 diagnostics today, then fail `go vet` / `go build` with
//! `cannot use 300 as int8 value (overflows)`. The accepted-should-
//! emit-buildable-Go contract requires a checker diagnostic (HYB-E6002)
//! for that narrow constant case. Non-constant operands stay out of
//! scope — Go truncates at run time via an explicit conversion
//! (SPEC-LANGUAGE X4), and the conversion form `int8(x)` is unaffected.

use crate::model::{unwrap_parens, Checker, FnState};
use hy_diag::{Diagnostic, Span};
use hy_syntax::{BinOp, Decl, Expr, LitKind, TypeExpr, UnOp};

impl<'a> Checker<'a> {
    /// When `ty` is a fixed-width integer and `value` is an integer
    /// constant outside that type's range (or a float constant that would
    /// truncate), emit HYB-E6002.
    pub(crate) fn check_const_overflow_init(&mut self, name: &str, ty: &TypeExpr, value: &Expr) {
        let TypeExpr::Named {
            name: ty_name,
            span: ty_span,
        } = ty
        else {
            return;
        };
        let resolved_name = self.resolve_type_alias_name(ty_name);
        let Some((lo, hi)) = fixed_width_int_range(resolved_name) else {
            return;
        };
        if is_float_const_expr(value) {
            let span = value.span();
            let msg = format!(
                "constant `{}` truncated to integer type `{}` of `{}` (HYB-E6002)",
                value.render(),
                ty_name,
                name
            );
            let notes = vec![
                format!(
                    "why: Go rejects a floating-point constant initializer for `{}` (`cannot use … as {} value in variable declaration (truncated)`), so an accepted Hybrid program would emit unbuildable Go (issue #201)",
                    ty_name, ty_name
                ),
                format!(
                    "fix: use an integer constant in [{}, {}], or declare `{}` with a floating-point type (`float64` / `float32`)",
                    lo, hi, name
                ),
                format!(
                    "note: the declared type was written here ({})",
                    span_hint(*ty_span)
                ),
            ];
            self.diags.push(
                Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
            );
            return;
        }
        let Some(v) = self.eval_const_int(None, value, 0) else {
            return;
        };
        if v >= lo && v <= hi {
            return;
        }
        let span = value.span();
        let msg = format!(
            "constant `{}` overflows declared type `{}` of `{}` (HYB-E6002)",
            value.render(),
            ty_name,
            name
        );
        let notes = vec![
            format!(
                "why: Go rejects a constant initializer outside `{}`'s range (`cannot use … as {} value (overflows)`), so an accepted Hybrid program would emit unbuildable Go (issue #148 / #201)",
                ty_name, ty_name
            ),
            format!(
                "fix: use a constant in [{}, {}], widen the declared type, or convert from a variable if truncation is intentional (`x := {}; y := {}(x)`)",
                lo, hi, value.render(), ty_name
            ),
            format!(
                "note: the declared type was written here ({})",
                span_hint(*ty_span)
            ),
        ];
        self.diags.push(
            Diagnostic::error("HYB-E6002", self.path.clone(), span, msg).with_notes(notes),
        );
    }

    pub(crate) fn resolve_type_alias_name<'s>(&'s self, name: &'s str) -> &'s str {
        let mut cur = name;
        for _ in 0..8 {
            let next = self.file.decls.iter().find_map(|d| match d {
                Decl::TypeAlias(ta) if ta.name == cur => match &ta.ty {
                    TypeExpr::Named { name: target, .. } => Some(target.as_str()),
                    _ => None,
                },
                _ => None,
            });
            match next {
                Some(n) => cur = n,
                None => break,
            }
        }
        cur
    }

    /// Evaluate a compile-time integer constant expression, resolving
    /// file-level `const` bindings (when not shadowed by a runtime binding in `st`).
    pub(crate) fn eval_const_int(
        &self,
        st: Option<&FnState>,
        e: &Expr,
        depth: usize,
    ) -> Option<i128> {
        if depth > 32 {
            return None;
        }
        match unwrap_parens(e) {
            Expr::Ident { name, .. } => {
                if let Some(s) = st {
                    if let Some(b) = s.env_lookup(name) {
                        if !b.immutable {
                            return None;
                        }
                        if let Some(val) = self.find_local_const_value(name) {
                            return self.eval_const_int(st, val, depth + 1);
                        }
                    }
                }
                for d in &self.file.decls {
                    if let Decl::Const(c) = d {
                        if c.name == *name {
                            return self.eval_const_int(None, &c.value, depth + 1);
                        }
                    }
                }
                if st.is_none() {
                    if let Some(val) = self.find_local_const_value(name) {
                        return self.eval_const_int(None, val, depth + 1);
                    }
                }
                None
            }
            Expr::Unary {
                op: UnOp::Neg,
                operand,
                ..
            } => {
                let v = self.eval_const_int(st, operand, depth + 1)?;
                Some(v.saturating_neg())
            }
            Expr::Binary { op, lhs, rhs, .. } => {
                let l = self.eval_const_int(st, lhs, depth + 1)?;
                let r = self.eval_const_int(st, rhs, depth + 1)?;
                eval_bin_int(*op, l, r)
            }
            other => const_int_value(other),
        }
    }

    fn find_local_const_value(&self, target: &str) -> Option<&'a Expr> {
        for f in self.file.fns() {
            if let Some(body) = &f.body {
                if let Some(e) = find_const_in_block(body, target) {
                    return Some(e);
                }
            }
        }
        None
    }
}

fn find_const_in_block<'a>(block: &'a hy_syntax::Block, target: &str) -> Option<&'a Expr> {
    for stmt in &block.stmts {
        if let Some(e) = find_const_in_stmt(stmt, target) {
            return Some(e);
        }
    }
    None
}

fn find_const_in_stmt<'a>(stmt: &'a hy_syntax::Stmt, target: &str) -> Option<&'a Expr> {
    use hy_syntax::{LocalKind, Stmt};
    match stmt {
        Stmt::Local(l) if l.kind == LocalKind::Const => {
            for (n, v) in l.names.iter().zip(l.values.iter()) {
                if n == target {
                    return Some(v);
                }
            }
            None
        }
        Stmt::If {
            init,
            then,
            otherwise,
            ..
        } => {
            if let Some(i) = init {
                if let Some(e) = find_const_in_stmt(i, target) {
                    return Some(e);
                }
            }
            if let Some(e) = find_const_in_block(then, target) {
                return Some(e);
            }
            if let Some(o) = otherwise {
                if let Some(e) = find_const_in_stmt(o, target) {
                    return Some(e);
                }
            }
            None
        }
        Stmt::For { body, .. } | Stmt::Managed { body, .. } => find_const_in_block(body, target),
        Stmt::Block { block, .. } => find_const_in_block(block, target),
        Stmt::Match { arms, .. } => {
            for arm in arms {
                if let Some(e) = find_const_in_block(&arm.body, target) {
                    return Some(e);
                }
            }
            None
        }
        Stmt::Select { arms, .. } => {
            for arm in arms {
                if let Some(e) = find_const_in_block(&arm.body, target) {
                    return Some(e);
                }
            }
            None
        }
        _ => None,
    }
}

fn span_hint(span: Span) -> String {
    format!("{}:{}", span.start.line, span.start.col)
}

/// Inclusive representable range for a Hybrid fixed-width integer type
/// name (SPEC-LANGUAGE §11 / Go's typed-constant assignment rule).
/// Platform-word `int`/`uint`/`isize`/`usize` use the 64-bit LP64 ranges
/// the emitter targets (SPEC B9 / X7).
fn fixed_width_int_range(name: &str) -> Option<(i128, i128)> {
    Some(match name {
        "i8" | "int8" => (i8::MIN as i128, i8::MAX as i128),
        "u8" | "uint8" | "byte" => (0, u8::MAX as i128),
        "i16" | "int16" => (i16::MIN as i128, i16::MAX as i128),
        "u16" | "uint16" => (0, u16::MAX as i128),
        "i32" | "int32" | "rune" => (i32::MIN as i128, i32::MAX as i128),
        "u32" | "uint32" => (0, u32::MAX as i128),
        "i64" | "int64" | "int" | "isize" => (i64::MIN as i128, i64::MAX as i128),
        "u64" | "uint64" | "uint" | "usize" | "uintptr" => (0, u64::MAX as i128),
        _ => return None,
    })
}

fn is_float_const_expr(e: &Expr) -> bool {
    match unwrap_parens(e) {
        Expr::Lit {
            kind: LitKind::Float(_),
            ..
        } => true,
        Expr::Unary {
            op: UnOp::Neg,
            operand,
            ..
        } => is_float_const_expr(operand),
        Expr::Binary { lhs, rhs, .. } => is_float_const_expr(lhs) || is_float_const_expr(rhs),
        _ => false,
    }
}

fn eval_bin_int(op: BinOp, l: i128, r: i128) -> Option<i128> {
    match op {
        BinOp::Add => Some(l.saturating_add(r)),
        BinOp::Sub => Some(l.saturating_sub(r)),
        BinOp::Mul => Some(l.saturating_mul(r)),
        BinOp::Div => {
            if r == 0 {
                None
            } else {
                Some(l.saturating_div(r))
            }
        }
        BinOp::Mod => {
            if r == 0 {
                None
            } else {
                l.checked_rem(r)
            }
        }
        BinOp::BitOr => Some(l | r),
        BinOp::BitXor => Some(l ^ r),
        BinOp::BitAnd => Some(l & r),
        BinOp::Shl => {
            if r < 0 {
                None
            } else if r >= 127 {
                Some(if l > 0 {
                    i128::MAX
                } else if l < 0 {
                    i128::MIN
                } else {
                    0
                })
            } else {
                let sh = r as u32;
                let shifted = l.checked_shl(sh).unwrap_or(if l >= 0 {
                    i128::MAX
                } else {
                    i128::MIN
                });
                if l > 0 && shifted <= 0 {
                    Some(i128::MAX)
                } else if l < 0 && shifted >= 0 {
                    Some(i128::MIN)
                } else {
                    Some(shifted)
                }
            }
        }
        BinOp::Shr => {
            if r < 0 {
                None
            } else if r >= 127 {
                Some(if l < 0 { -1 } else { 0 })
            } else {
                l.checked_shr(r as u32)
            }
        }
        _ => None,
    }
}

/// Evaluate a pure integer constant expression the checker can see without
/// a full constant folder: int literals (any base the lexer keeps),
/// unary `-`, integer binary ops, and parentheses.
pub(crate) fn const_int_value(e: &Expr) -> Option<i128> {
    match unwrap_parens(e) {
        Expr::Lit {
            kind: LitKind::Int(s),
            ..
        } => parse_int_lit(s),
        Expr::Unary {
            op: UnOp::Neg,
            operand,
            ..
        } => {
            let v = const_int_value(operand)?;
            Some(v.saturating_neg())
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            let l = const_int_value(lhs)?;
            let r = const_int_value(rhs)?;
            eval_bin_int(*op, l, r)
        }
        _ => None,
    }
}

fn parse_int_lit(s: &str) -> Option<i128> {
    let clean: String = s.chars().filter(|c| *c != '_').collect();
    let s = clean.as_bytes();
    if s.is_empty() {
        return None;
    }
    if s.len() >= 2 && s[0] == b'0' {
        match s[1].to_ascii_lowercase() {
            b'x' => return i128::from_str_radix(std::str::from_utf8(&s[2..]).ok()?, 16).ok(),
            b'b' => return i128::from_str_radix(std::str::from_utf8(&s[2..]).ok()?, 2).ok(),
            b'o' => return i128::from_str_radix(std::str::from_utf8(&s[2..]).ok()?, 8).ok(),
            _ => {}
        }
    }
    i128::from_str_radix(std::str::from_utf8(s).ok()?, 10).ok()
}

#[cfg(test)]
mod unit {
    use super::*;

    #[test]
    fn ranges_match_go_fixed_width() {
        assert_eq!(fixed_width_int_range("int8"), Some((-128, 127)));
        assert_eq!(fixed_width_int_range("byte"), Some((0, 255)));
        assert_eq!(fixed_width_int_range("u16"), Some((0, 65535)));
        assert!(fixed_width_int_range("string").is_none());
        assert!(fixed_width_int_range("float64").is_none());
    }

    #[test]
    fn parse_bases() {
        assert_eq!(parse_int_lit("300"), Some(300));
        assert_eq!(parse_int_lit("0x12C"), Some(300));
        assert_eq!(parse_int_lit("0b101"), Some(5));
        assert_eq!(parse_int_lit("0o10"), Some(8));
    }
}
