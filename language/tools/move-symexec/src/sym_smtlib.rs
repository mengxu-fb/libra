// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{ffi::CString, os::raw::c_uint};

use crate::deps_z3::*;

/// Possibe results from the sat solver
pub enum SmtResult {
    SAT,
    UNSAT,
    UNKNOWN,
}

/// A context manager for all smt-related stuff
#[derive(Debug, Eq, PartialEq)]
pub struct SmtCtxt {
    /// A wrapper over Z3_context
    ctxt: Z3_context,
    /// Whether to simplify terms automatically
    conf_auto_simplify: bool,
}
// TODO: make SmtCtxt, SmtKind, SmtExpr all pub(crate)

impl SmtCtxt {
    pub fn new(conf_auto_simplify: bool) -> Self {
        let ctxt = unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            ctx
        };

        Self {
            ctxt,
            conf_auto_simplify,
        }
    }

    // create bools
    pub fn bool_const(&self, val: bool) -> SmtExpr {
        let ast = if val {
            unsafe { Z3_mk_true(self.ctxt) }
        } else {
            unsafe { Z3_mk_false(self.ctxt) }
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind: SmtKind::Bool,
        }
    }

    pub fn bool_var(&self, var: &str) -> SmtExpr {
        let kind = SmtKind::Bool;
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    // create bitvecs
    fn bitvec_const<T: ToString>(&self, val: T, signed: bool, width: u16) -> SmtExpr {
        let kind = SmtKind::Bitvec { signed, width };
        let str_repr = CString::new(val.to_string()).unwrap();
        let ast = unsafe { Z3_mk_numeral(self.ctxt, str_repr.as_ptr(), kind.to_z3_sort(self)) };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    pub fn bitvec_const_u8(&self, val: u8) -> SmtExpr {
        self.bitvec_const(val, false, 8)
    }

    pub fn bitvec_const_u64(&self, val: u64) -> SmtExpr {
        self.bitvec_const(val, false, 64)
    }

    pub fn bitvec_const_u128(&self, val: u128) -> SmtExpr {
        self.bitvec_const(val, false, 128)
    }

    fn bitvec_var(&self, var: &str, signed: bool, width: u16) -> SmtExpr {
        let kind = SmtKind::Bitvec { signed, width };
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    pub fn bitvec_var_u8(&self, var: &str) -> SmtExpr {
        self.bitvec_var(var, false, 8)
    }

    pub fn bitvec_var_u64(&self, var: &str) -> SmtExpr {
        self.bitvec_var(var, false, 64)
    }

    pub fn bitvec_var_u128(&self, var: &str) -> SmtExpr {
        self.bitvec_var(var, false, 128)
    }

    // create vectors (i.e., sequences)
    pub fn vector_const(&self, element_kind: &SmtKind, vals: &[&SmtExpr]) -> SmtExpr {
        debug_assert!(vals.iter().all(|expr| expr.kind == *element_kind));

        let kind = SmtKind::Vector {
            element_kind: Box::new(element_kind.clone()),
        };
        let unit_exprs: Vec<Z3_ast> = vals
            .iter()
            .map(|expr| unsafe { Z3_mk_seq_unit(self.ctxt, expr.ast) })
            .collect();
        let ast =
            unsafe { Z3_mk_seq_concat(self.ctxt, unit_exprs.len() as c_uint, unit_exprs.as_ptr()) };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    pub fn vector_var(&self, element_kind: &SmtKind, var: &str) -> SmtExpr {
        let kind = SmtKind::Vector {
            element_kind: Box::new(element_kind.clone()),
        };
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, kind.to_z3_sort(self))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind,
        }
    }

    // simplification
    fn simplify(&self, ast: Z3_ast, _kind: &SmtKind) -> Z3_ast {
        // TODO: in theory, we could have dedicated simplification
        // procedures depending on the kind of the ast. But for now,
        // let's just use the default simplification procedure in Z3
        unsafe { Z3_simplify(self.ctxt, ast) }
    }

    // post-processing for an ast out of some operation
    fn postprocess(&self, ast: Z3_ast, kind: &SmtKind) -> Z3_ast {
        if self.conf_auto_simplify {
            self.simplify(ast, kind)
        } else {
            ast
        }
    }

    // sat solving
    pub fn solve(&self, constraints: &[&SmtExpr]) -> SmtResult {
        let asts: Vec<Z3_ast> = constraints.iter().map(|expr| expr.ast).collect();
        let result = unsafe {
            let solver = Z3_mk_solver(self.ctxt);
            Z3_solver_check_assumptions(self.ctxt, solver, asts.len() as c_uint, asts.as_ptr())
        };

        // convert to enum
        if result == Z3_lbool_Z3_L_TRUE {
            SmtResult::SAT
        } else if result == Z3_lbool_Z3_L_FALSE {
            SmtResult::UNSAT
        } else {
            debug_assert_eq!(result, Z3_lbool_Z3_L_UNDEF);
            SmtResult::UNKNOWN
        }
    }
}

impl Drop for SmtCtxt {
    fn drop(&mut self) {
        unsafe {
            Z3_del_context(self.ctxt);
        }
    }
}

/// Make the type of SmtExpr explicit
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmtKind {
    Bool,
    Bitvec { signed: bool, width: u16 },
    Vector { element_kind: Box<SmtKind> },
    // TODO: more types to be added
}

impl SmtKind {
    // z3 linkage
    fn to_z3_sort(&self, ctxt: &SmtCtxt) -> Z3_sort {
        match self {
            SmtKind::Bool => unsafe { Z3_mk_bool_sort(ctxt.ctxt) },
            SmtKind::Bitvec { width, .. } => unsafe { Z3_mk_bv_sort(ctxt.ctxt, *width as c_uint) },
            SmtKind::Vector { element_kind } => unsafe {
                Z3_mk_seq_sort(ctxt.ctxt, element_kind.to_z3_sort(ctxt))
            },
        }
    }

    // shortcuts
    pub fn bitvec_u8() -> Self {
        SmtKind::Bitvec {
            signed: false,
            width: 8,
        }
    }

    pub fn bitvec_u64() -> Self {
        SmtKind::Bitvec {
            signed: false,
            width: 64,
        }
    }

    pub fn bitvec_u128() -> Self {
        SmtKind::Bitvec {
            signed: false,
            width: 128,
        }
    }
}

/// A wrapper over Z3_ast
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmtExpr<'a> {
    ast: Z3_ast,
    ctxt: &'a SmtCtxt,
    kind: SmtKind,
}

macro_rules! smt_unary_op_bool {
    ($func:tt, $expr:ident) => {{
        $expr.check_unary_op_bool();

        let ctxt = $expr.ctxt;
        let ast = unsafe { $func(ctxt.ctxt, $expr.ast) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bool {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bool($rhs);

        let ctxt = $lhs.ctxt;
        let terms: [Z3_ast; 2] = [$lhs.ast, $rhs.ast];
        let ast = unsafe { $func(ctxt.ctxt, 2, terms.as_ptr()) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bitvec_to_bitvec {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bitvec($rhs);

        let ctxt = $lhs.ctxt;
        let ast = unsafe { $func(ctxt.ctxt, $lhs.ast, $rhs.ast) };

        let kind = $lhs.kind.clone();
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bitvec_to_bitvec_sign_split {
    ($func_s:tt, $func_u:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bitvec($rhs);

        let ctxt = $lhs.ctxt;
        let ast = if matches!($lhs.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { $func_s(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        } else {
            unsafe { $func_u(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        };

        let kind = $lhs.kind.clone();
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_bitvec_to_bool_sign_split {
    ($func_s:tt, $func_u:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op_bitvec($rhs);

        let ctxt = $lhs.ctxt;
        let ast = if matches!($lhs.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { $func_s(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        } else {
            unsafe { $func_u(ctxt.ctxt, $lhs.ast, $rhs.ast) }
        };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_generic_to_bool {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op($rhs);

        let ctxt = $lhs.ctxt;
        let ast = unsafe { $func(ctxt.ctxt, $lhs.ast, $rhs.ast) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

macro_rules! smt_binary_op_generic_to_bool_by_term {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        $lhs.check_binary_op($rhs);

        let ctxt = $lhs.ctxt;
        let terms: [Z3_ast; 2] = [$lhs.ast, $rhs.ast];
        let ast = unsafe { $func(ctxt.ctxt, 2, terms.as_ptr()) };

        let kind = SmtKind::Bool;
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }};
}

impl<'a> SmtExpr<'a> {
    // checking
    fn check_unary_op_bool(&self) {
        debug_assert!(matches!(self.kind, SmtKind::Bool));
    }

    fn check_unary_op_bitvec(&self) {
        debug_assert!(matches!(self.kind, SmtKind::Bitvec { .. }));
    }

    fn check_binary_op(&self, rhs: &SmtExpr<'a>) {
        debug_assert_eq!(self.ctxt, rhs.ctxt);
        debug_assert_eq!(self.kind, rhs.kind);
    }

    fn check_binary_op_bool(&self, rhs: &SmtExpr<'a>) {
        self.check_binary_op(rhs);
        debug_assert!(matches!(self.kind, SmtKind::Bool));
    }

    fn check_binary_op_bitvec(&self, rhs: &SmtExpr<'a>) {
        self.check_binary_op(rhs);
        debug_assert!(matches!(self.kind, SmtKind::Bitvec { .. }));
    }

    // bool logic operators
    pub fn not(&self) -> SmtExpr<'a> {
        smt_unary_op_bool!(Z3_mk_not, self)
    }

    pub fn and(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bool!(Z3_mk_and, self, rhs)
    }

    pub fn or(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bool!(Z3_mk_or, self, rhs)
    }

    // bitvec arith operators
    pub fn add(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvadd, self, rhs)
    }

    pub fn sub(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvsub, self, rhs)
    }

    pub fn mul(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvmul, self, rhs)
    }

    pub fn div(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec_sign_split!(Z3_mk_bvsdiv, Z3_mk_bvudiv, self, rhs)
    }

    pub fn rem(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec_sign_split!(Z3_mk_bvsmod, Z3_mk_bvurem, self, rhs)
    }

    // bitvec casting operators
    fn cast(&self, into_signed: bool, into_width: u16) -> SmtExpr<'a> {
        self.check_unary_op_bitvec();

        let ctxt = self.ctxt;
        let ast = match self.kind {
            SmtKind::Bitvec { width, .. } => {
                if width < into_width {
                    if into_signed {
                        unsafe {
                            Z3_mk_sign_ext(ctxt.ctxt, (into_width - width) as c_uint, self.ast)
                        }
                    } else {
                        unsafe {
                            Z3_mk_zero_ext(ctxt.ctxt, (into_width - width) as c_uint, self.ast)
                        }
                    }
                } else if width > into_width {
                    unsafe { Z3_mk_extract(ctxt.ctxt, (into_width - 1) as c_uint, 0, self.ast) }
                } else {
                    self.ast
                }
            }
            _ => panic!("Cast is only applicable to bitvec"),
        };

        let kind = SmtKind::Bitvec {
            signed: into_signed,
            width: into_width,
        };
        let ast = ctxt.postprocess(ast, &kind);
        SmtExpr { ast, ctxt, kind }
    }

    pub fn cast_u8(&self) -> SmtExpr<'a> {
        self.cast(false, 8)
    }

    pub fn cast_u64(&self) -> SmtExpr<'a> {
        self.cast(false, 64)
    }

    pub fn cast_u128(&self) -> SmtExpr<'a> {
        self.cast(false, 128)
    }

    // bitvec bitwise operators
    pub fn bit_and(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvand, self, rhs)
    }

    pub fn bit_or(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvor, self, rhs)
    }

    pub fn bit_xor(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvxor, self, rhs)
    }

    pub fn shl(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec!(Z3_mk_bvshl, self, rhs)
    }

    pub fn shr(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bitvec_sign_split!(Z3_mk_bvashr, Z3_mk_bvlshr, self, rhs)
    }

    // bitvec comparison operators
    pub fn gt(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvsgt, Z3_mk_bvugt, self, rhs)
    }

    pub fn ge(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvsge, Z3_mk_bvuge, self, rhs)
    }

    pub fn le(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvsle, Z3_mk_bvule, self, rhs)
    }

    pub fn lt(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_bitvec_to_bool_sign_split!(Z3_mk_bvslt, Z3_mk_bvult, self, rhs)
    }

    // equality operator (for both bool and bitvec)
    pub fn eq(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_generic_to_bool!(Z3_mk_eq, self, rhs)
    }

    pub fn ne(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        smt_binary_op_generic_to_bool_by_term!(Z3_mk_distinct, self, rhs)
    }
}

// unit testing for the smtlib
#[cfg(test)]
mod tests {
    use super::*;

    fn ctxt_variants() -> Vec<SmtCtxt> {
        vec![SmtCtxt::new(true), SmtCtxt::new(false)]
    }

    macro_rules! prove {
        ($ctxt:ident, $pat_true:pat, $pat_false:pat, $pred:expr) => {
            assert!(matches!(
                $ctxt.solve(&[$pred]),
                $pat_true
            ));
            assert!(matches!(
                $ctxt.solve(&[&$pred.not()]),
                $pat_false
            ));
        };
        ($ctxt: ident, $pat_true:pat, $pat_false:pat, $pred:expr, $( $cond:expr ),+) => {
            assert!(matches!(
                $ctxt.solve(&[$pred, $( $cond ),+]),
                $pat_true
            ));
            assert!(matches!(
                $ctxt.solve(&[
                    &[$( $cond ),+]
                        .iter()
                        .fold($pred.clone(), |acc, cur| {acc.and(cur)})
                        .not()
                ]),
                $pat_false
            ));
        };
    }

    macro_rules! prove_true {
        ($ctxt:ident, $pred:expr) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::UNSAT, $pred)
        };
        ($ctxt: ident, $pred:expr, $( $cond:expr ),+) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::UNSAT, $pred, $( $cond ),+)
        };
    }

    macro_rules! prove_false {
        ($ctxt:ident, $pred:expr) => {
            prove!($ctxt, SmtResult::UNSAT, SmtResult::SAT, $pred)
        };
        ($ctxt: ident, $pred:expr, $( $cond:expr ),+) => {
            prove!($ctxt, SmtResult::UNSAT, SmtResult::SAT, $pred, $( $cond ),+)
        };
    }

    macro_rules! prove_maybe {
        ($ctxt:ident, $pred:expr) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::SAT, $pred)
        };
        ($ctxt: ident, $pred:expr, $( $cond:expr ),+) => {
            prove!($ctxt, SmtResult::SAT, SmtResult::SAT, $pred, $( $cond ),+)
        };
    }

    macro_rules! prove_eq {
        ($ctxt:ident, $lhs:expr, $rhs:expr) => {
            prove_true!($ctxt, &$lhs.eq($rhs));
        };
    }

    macro_rules! prove_ne {
        ($ctxt:ident, $lhs:expr, $rhs:expr) => {
            prove_true!($ctxt, &$lhs.ne($rhs));
        };
    }

    macro_rules! prove_qn {
        ($ctxt:ident, $lhs:expr, $rhs:expr) => {
            prove_maybe!($ctxt, &$lhs.eq($rhs));
            prove_maybe!($ctxt, &$lhs.ne($rhs));
        };
    }

    #[test]
    fn test_bool() {
        for ctxt in ctxt_variants().iter() {
            // a true constant
            let expr_t = ctxt.bool_const(true);
            prove_true!(ctxt, &expr_t);

            // a false constant
            let expr_f = ctxt.bool_const(false);
            prove_false!(ctxt, &expr_f);

            // a variable
            let expr_x = ctxt.bool_var("x");
            prove_maybe!(ctxt, &expr_x);

            // NOT
            prove_false!(ctxt, &expr_t.not());
            prove_true!(ctxt, &expr_f.not());
            prove_maybe!(ctxt, &expr_x.not());

            // AND
            prove_true!(ctxt, &expr_t.and(&expr_t));
            prove_false!(ctxt, &expr_t.and(&expr_f));
            prove_false!(ctxt, &expr_f.and(&expr_t));
            prove_false!(ctxt, &expr_f.and(&expr_f));
            prove_maybe!(ctxt, &expr_t.and(&expr_x));
            prove_false!(ctxt, &expr_f.and(&expr_x));

            // OR
            prove_true!(ctxt, &expr_t.or(&expr_t));
            prove_true!(ctxt, &expr_t.or(&expr_f));
            prove_true!(ctxt, &expr_f.or(&expr_t));
            prove_false!(ctxt, &expr_f.or(&expr_f));
            prove_true!(ctxt, &expr_t.or(&expr_x));
            prove_maybe!(ctxt, &expr_f.or(&expr_x));
        }
    }

    #[test]
    fn test_bitvec() {
        // since Move has unsigned integers only, we focus on the
        // test of unsigned integer as well
        for ctxt in ctxt_variants().iter() {
            // constants
            let expr_u8_0 = ctxt.bitvec_const_u8(0);
            let expr_u8_1 = ctxt.bitvec_const_u8(1);
            let expr_u8_255 = ctxt.bitvec_const_u8(255);

            // variable
            let expr_u8_x = ctxt.bitvec_var_u8("x");
            prove_qn!(ctxt, &expr_u8_x, &expr_u8_0);

            // ADD
            prove_eq!(ctxt, &expr_u8_0.add(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.add(&expr_u8_1), &expr_u8_1);
            prove_eq!(ctxt, &expr_u8_0.add(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_1.add(&expr_u8_x), &expr_u8_x); // may overflow
            prove_ne!(ctxt, &expr_u8_255.add(&expr_u8_x), &expr_u8_x); // may overflow

            // SUB
            prove_eq!(ctxt, &expr_u8_0.sub(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.sub(&expr_u8_1), &expr_u8_255);
            prove_qn!(ctxt, &expr_u8_0.sub(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_1.sub(&expr_u8_x), &expr_u8_x); // may overflow
            prove_ne!(ctxt, &expr_u8_255.add(&expr_u8_x), &expr_u8_x); // may overflow

            // MUL
            prove_eq!(ctxt, &expr_u8_0.mul(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.mul(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.mul(&expr_u8_x), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_1.mul(&expr_u8_x), &expr_u8_x); // may overflow
            prove_qn!(ctxt, &expr_u8_255.mul(&expr_u8_x), &expr_u8_x); // may overflow

            // DIV
            prove_ne!(ctxt, &expr_u8_0.div(&expr_u8_0), &expr_u8_0); // div by zero
            prove_eq!(ctxt, &expr_u8_0.div(&expr_u8_1), &expr_u8_0);
            prove_qn!(ctxt, &expr_u8_0.div(&expr_u8_x), &expr_u8_0); // may div by zero
            prove_qn!(ctxt, &expr_u8_1.div(&expr_u8_x), &expr_u8_x); // may div by zero
            prove_ne!(ctxt, &expr_u8_255.div(&expr_u8_x), &expr_u8_x); // may div by zero

            // MOD
            prove_eq!(ctxt, &expr_u8_0.rem(&expr_u8_0), &expr_u8_0); // div by zero
            prove_eq!(ctxt, &expr_u8_0.rem(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.rem(&expr_u8_x), &expr_u8_0); // may div by zero
            prove_ne!(ctxt, &expr_u8_1.rem(&expr_u8_x), &expr_u8_x); // may div by zero
            prove_ne!(ctxt, &expr_u8_255.rem(&expr_u8_x), &expr_u8_x); // may div by zero

            // BIT_AND
            prove_eq!(ctxt, &expr_u8_0.bit_and(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_and(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_and(&expr_u8_x), &expr_u8_0);
            prove_qn!(ctxt, &expr_u8_1.bit_and(&expr_u8_x), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_255.bit_and(&expr_u8_x), &expr_u8_x);

            // BIT_OR
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_1), &expr_u8_1);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_x), &expr_u8_x);
            prove_qn!(ctxt, &expr_u8_1.bit_or(&expr_u8_x), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_255.bit_or(&expr_u8_x), &expr_u8_255);

            // BIT_XOR
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_1), &expr_u8_1);
            prove_eq!(ctxt, &expr_u8_0.bit_or(&expr_u8_x), &expr_u8_x);
            prove_qn!(ctxt, &expr_u8_1.bit_or(&expr_u8_x), &expr_u8_x);
            prove_qn!(ctxt, &expr_u8_255.bit_or(&expr_u8_x), &expr_u8_x);

            // SHL
            prove_eq!(ctxt, &expr_u8_0.shl(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.shl(&expr_u8_1), &expr_u8_0);
            prove_qn!(ctxt, &expr_u8_0.shl(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_1.shl(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_255.shl(&expr_u8_x), &expr_u8_x);

            // SHR
            prove_eq!(ctxt, &expr_u8_0.shr(&expr_u8_0), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.shr(&expr_u8_1), &expr_u8_0);
            prove_eq!(ctxt, &expr_u8_0.shr(&expr_u8_x), &expr_u8_0);
            prove_ne!(ctxt, &expr_u8_1.shr(&expr_u8_x), &expr_u8_x);
            prove_ne!(ctxt, &expr_u8_255.shr(&expr_u8_x), &expr_u8_x);

            // GT
            prove_false!(ctxt, &expr_u8_0.gt(&expr_u8_0));
            prove_false!(ctxt, &expr_u8_0.gt(&expr_u8_1));
            prove_false!(ctxt, &expr_u8_0.gt(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.gt(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_255.gt(&expr_u8_x));

            // GE
            prove_true!(ctxt, &expr_u8_0.ge(&expr_u8_0));
            prove_false!(ctxt, &expr_u8_0.ge(&expr_u8_1));
            prove_maybe!(ctxt, &expr_u8_0.ge(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.ge(&expr_u8_x));
            prove_true!(ctxt, &expr_u8_255.ge(&expr_u8_x));

            // LE
            prove_true!(ctxt, &expr_u8_0.le(&expr_u8_0));
            prove_true!(ctxt, &expr_u8_0.le(&expr_u8_1));
            prove_true!(ctxt, &expr_u8_0.le(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.le(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_255.le(&expr_u8_x));

            // LT
            prove_false!(ctxt, &expr_u8_0.lt(&expr_u8_0));
            prove_true!(ctxt, &expr_u8_0.lt(&expr_u8_1));
            prove_maybe!(ctxt, &expr_u8_0.lt(&expr_u8_x));
            prove_maybe!(ctxt, &expr_u8_1.lt(&expr_u8_x));
            prove_false!(ctxt, &expr_u8_255.lt(&expr_u8_x));

            // CAST
            prove_eq!(ctxt, &expr_u8_x.cast_u8(), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_x.cast_u64().cast_u8(), &expr_u8_x);
            prove_eq!(ctxt, &expr_u8_x.cast_u128().cast_u8(), &expr_u8_x);
        }
    }

    #[test]
    fn test_vector() {
        for ctxt in ctxt_variants().iter() {
            // constants
            let expr_u8_0 = ctxt.bitvec_const_u8(0);
            let expr_u8_1 = ctxt.bitvec_const_u8(1);
            let expr_vec_u8_00_01 =
                ctxt.vector_const(&SmtKind::bitvec_u8(), &[&expr_u8_0, &expr_u8_1]);
            prove_eq!(ctxt, &expr_vec_u8_00_01, &expr_vec_u8_00_01);

            // variable
            let expr_vec_u8_x = ctxt.vector_var(&SmtKind::bitvec_u8(), "x");
            prove_eq!(ctxt, &expr_vec_u8_x, &expr_vec_u8_x);

            // EQ || NE
            prove_qn!(ctxt, &expr_vec_u8_00_01, &expr_vec_u8_x);
        }
    }
}
