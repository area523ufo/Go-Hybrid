//! Regression tests for issue #201:
//! Five accepted-but-unbuildable families that previously passed `hyb check`
//! with 0 diagnostics and then failed `go vet` / `go build`:
//!   * Sub-family A (A1–A4): `==`/`!=` on incomparable types (map, slice,
//!     function/closure, and struct/array containing an incomparable field).
//!   * Sub-family B (B1–B4): `var`/`const` ascription of overflowing binary
//!     constant expressions (`100 + 100`, `1 << 10`), float truncation to an
//!     integer type (`var x int = 2.5`), and negative shift counts (`1 << -1`).
//!   * Sub-family C (C1–C4): redeclarations of top-level functions, constants,
//!     struct fields, and methods on the same receiver type.
//!   * Sub-family D (D1–D2): invalid method receiver types (built-in/non-local
//!     types like `int` and double pointers `**T`).
//!   * Sub-family E (E1–E2): negative (`[-1]int`) and non-constant (`[n]int`)
//!     array lengths.

use hy_check::{check_file, Verdict};
use hy_diag::Severity;
use hy_syntax::parse_file;

fn check(src: &str) -> hy_check::CheckResult {
    let ast = parse_file("test.hy", src)
        .unwrap_or_else(|diags| panic!("must parse (parser contract): {:?}", diags));
    check_file(&ast)
}

fn error_codes(r: &hy_check::CheckResult) -> Vec<String> {
    r.diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| d.code.clone())
        .collect()
}

// ===========================================================================
// Sub-family A — Equality `==` / `!=` on incomparable types
// ===========================================================================

#[test]
fn a1_map_equality_rejected() {
    let r = check(
        "fn main() {\n\
           m1 := map[string]int{\"a\": 1}\n\
           m2 := map[string]int{\"a\": 1}\n\
           if m1 == m2 {\n\
             x := 1\n\
             _ = x\n\
           }\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn a2_slice_equality_rejected() {
    let r = check(
        "fn main() {\n\
           s1 := []int{1, 2}\n\
           s2 := []int{1, 2}\n\
           if s1 == s2 {\n\
             x := 1\n\
             _ = x\n\
           }\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn a3_fn_and_closure_equality_rejected() {
    let r_fn = check(
        "fn helper() int { return 1 }\n\
         fn main() {\n\
           if helper == helper {\n\
             x := 1\n\
             _ = x\n\
           }\n\
         }\n",
    );
    assert_eq!(r_fn.verdict, Verdict::Reject, "{:?}", r_fn.diagnostics);
    assert!(error_codes(&r_fn).contains(&"HYB-E2001".to_string()));

    let r_clos = check(
        "fn main() {\n\
           f := fn() int { return 1 }\n\
           if f != f {\n\
             x := 1\n\
             _ = x\n\
           }\n\
         }\n",
    );
    assert_eq!(r_clos.verdict, Verdict::Reject, "{:?}", r_clos.diagnostics);
    assert!(error_codes(&r_clos).contains(&"HYB-E2001".to_string()));
}

#[test]
fn a4_struct_with_incomparable_field_equality_rejected() {
    let r = check(
        "struct holder {\n\
           f fn() int\n\
         }\n\
         fn main() {\n\
           var a holder\n\
           var b holder\n\
           if a == b {\n\
             x := 1\n\
             _ = x\n\
           }\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn a_positive_controls_comparable_types_accepted() {
    let r = check(
        "struct point {\n\
           x int\n\
           y int\n\
         }\n\
         fn main() {\n\
           p1 := point{x: 1, y: 2}\n\
           p2 := point{x: 1, y: 2}\n\
           ch1 := make(chan int, 1)\n\
           ch2 := ch1\n\
           s := \"ok\"\n\
           if p1 == p2 && ch1 == ch2 && s != \"no\" {\n\
             x := 1\n\
             _ = x\n\
           }\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
}

// ===========================================================================
// Sub-family B — Constant overflow / float truncation / negative shift count
// ===========================================================================

#[test]
fn b1_var_int8_binary_const_overflow_rejected() {
    let r = check(
        "fn main() {\n\
           var x int8 = 100 + 100\n\
           _ = x\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E6002".to_string()));
}

#[test]
fn b2_var_int8_shift_const_overflow_rejected() {
    let r = check(
        "fn main() {\n\
           var x int8 = 1 << 10\n\
           _ = x\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E6002".to_string()));
}

#[test]
fn b3_var_int_float_literal_truncation_rejected() {
    let r = check(
        "fn main() {\n\
           var x int = 2.5\n\
           _ = x\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E6002".to_string()));
}

#[test]
fn b4_negative_shift_count_rejected() {
    let r = check(
        "fn main() {\n\
           x := 1 << -1\n\
           _ = x\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E6002".to_string()));
}

#[test]
fn b_positive_controls_in_range_constants_accepted() {
    let r = check(
        "fn main() {\n\
           var a int8 = 50 + 50\n\
           var b int8 = 1 << 6\n\
           var c float64 = 2.5\n\
           d := 1 << 4\n\
           _ = a\n\
           _ = b\n\
           _ = c\n\
           _ = d\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
}

// ===========================================================================
// Sub-family C — Redeclarations in the same scope
// ===========================================================================

#[test]
fn c1_duplicate_toplevel_fn_rejected() {
    let r = check(
        "fn main() {\n\
           x := 1\n\
           _ = x\n\
         }\n\
         fn main() {\n\
           y := 2\n\
           _ = y\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn c2_duplicate_const_rejected() {
    let r = check(
        "const a = 1\n\
         const a = 2\n\
         fn main() {\n\
           _ = a\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn c3_duplicate_struct_field_rejected() {
    let r = check(
        "struct dup {\n\
           a int\n\
           a string\n\
         }\n\
         fn main() {\n\
           d := dup{a: 1}\n\
           _ = d\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn c4_duplicate_method_on_same_receiver_rejected() {
    let r = check(
        "struct box { x int }\n\
         fn (b box) get() int { return b.x }\n\
         fn (b box) get() int { return b.x + 1 }\n\
         fn main() {\n\
           b := box{x: 1}\n\
           _ = b.get()\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn c_positive_controls_different_receivers_and_inner_shadow_accepted() {
    let r = check(
        "struct box_a { x int }\n\
         struct box_b { x int }\n\
         fn (a box_a) get() int { return a.x }\n\
         fn (b box_b) get() int { return b.x }\n\
         fn main() {\n\
           x := 1\n\
           if true {\n\
             x := 2\n\
             _ = x\n\
           }\n\
           _ = x\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
}

// ===========================================================================
// Sub-family D — Invalid method receiver types
// ===========================================================================

#[test]
fn d1_method_on_builtin_int_rejected() {
    let r = check(
        "fn (c int) method() int {\n\
           return c\n\
         }\n\
         fn main() {\n\
           x := 1\n\
           _ = x\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn d2_method_on_double_pointer_rejected() {
    let r = check(
        "struct box { x int }\n\
         fn (b **box) get() int {\n\
           return 0\n\
         }\n\
         fn main() {\n\
           b := box{x: 1}\n\
           _ = b\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn d_positive_controls_value_and_pointer_struct_receivers_accepted() {
    let r = check(
        "struct box { x int }\n\
         fn (b box) get() int { return b.x }\n\
         fn (b *box) set(v int) { b.x = v }\n\
         fn main() {\n\
           b := box{x: 1}\n\
           b.set(2)\n\
           _ = b.get()\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
}

// ===========================================================================
// Sub-family E — Invalid array lengths
// ===========================================================================

#[test]
fn e1_negative_array_length_rejected() {
    let r = check(
        "fn main() {\n\
           var a [-1]int\n\
           _ = a\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E6002".to_string()));
}

#[test]
fn e2_non_constant_array_length_rejected() {
    let r = check(
        "fn main() {\n\
           n := 4\n\
           var a [n]int\n\
           _ = a\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Reject, "{:?}", r.diagnostics);
    assert!(error_codes(&r).contains(&"HYB-E2001".to_string()));
}

#[test]
fn e_positive_controls_literal_and_const_array_lengths_accepted() {
    let r = check(
        "const n_len = 4\n\
         fn main() {\n\
           const m_len = 2\n\
           var a [4]int\n\
           var b [n_len]int\n\
           var c [m_len + 1]int\n\
           _ = a\n\
           _ = b\n\
           _ = c\n\
         }\n",
    );
    assert_eq!(r.verdict, Verdict::Accept, "{:?}", r.diagnostics);
}
