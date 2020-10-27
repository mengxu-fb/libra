// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{ffi::CString, os::raw::c_uint};

use crate::deps_z3::*;

/// Possibe results from the sat solver
pub(crate) enum SmtResult {
    SAT,
    UNSAT,
    UNKNOWN,
}

/// A wrapper over Z3_context
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct SmtCtxt {
    ctxt: Z3_context,
}

impl SmtCtxt {
    pub fn new() -> Self {
        let ctxt = unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            ctx
        };

        Self { ctxt }
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
    pub fn vector_const(&self, element_kind: &SmtKind, vals: &[SmtExpr]) -> SmtExpr {
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
pub(crate) enum SmtKind {
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
}

/// A wrapper over Z3_ast
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SmtExpr<'a> {
    ast: Z3_ast,
    ctxt: &'a SmtCtxt,
    kind: SmtKind,
}

impl<'a> SmtExpr<'a> {
    // checking
    fn check_unary_op_bool(&self) {
        debug_assert!(matches!(self.kind, SmtKind::Bool));
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
    pub fn and(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bool(rhs);
        let terms: [Z3_ast; 2] = [self.ast, rhs.ast];
        let ast = unsafe { Z3_mk_and(self.ctxt.ctxt, 2, terms.as_ptr()) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn or(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bool(rhs);
        let terms: [Z3_ast; 2] = [self.ast, rhs.ast];
        let ast = unsafe { Z3_mk_or(self.ctxt.ctxt, 2, terms.as_ptr()) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn not(&self) -> SmtExpr<'a> {
        self.check_unary_op_bool();
        let ast = unsafe { Z3_mk_not(self.ctxt.ctxt, self.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    // bitvec arith operators
    pub fn add(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvadd(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn sub(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvsub(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn mul(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvmul(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn div(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvsdiv(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvudiv(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn rem(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvsmod(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvurem(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    // bitvec casting operators
    fn cast(&self, into_signed: bool, into_width: u16) -> SmtExpr<'a> {
        let ast = match self.kind {
            SmtKind::Bitvec { signed, width } => {
                if width < into_width {
                    if into_signed {
                        unsafe { Z3_mk_sign_ext(self.ctxt.ctxt, into_width as c_uint, self.ast) }
                    } else {
                        unsafe { Z3_mk_zero_ext(self.ctxt.ctxt, into_width as c_uint, self.ast) }
                    }
                } else if width > into_width {
                    unsafe {
                        Z3_mk_extract(self.ctxt.ctxt, (into_width - 1) as c_uint, 0, self.ast)
                    }
                } else {
                    self.ast
                }
            }
            _ => panic!("Cast is only applicable to bitvec"),
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bitvec {
                signed: into_signed,
                width: into_width,
            },
        }
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
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvand(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn bit_or(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvor(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn bit_xor(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvxor(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn shl(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = unsafe { Z3_mk_bvshl(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    pub fn shr(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvashr(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvlshr(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: self.kind.clone(),
        }
    }

    // bitvec comparison operators
    pub fn gt(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvsgt(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvugt(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bool,
        }
    }

    pub fn ge(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvsge(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvuge(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bool,
        }
    }

    pub fn le(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvsle(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvule(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bool,
        }
    }

    pub fn lt(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bitvec(rhs);
        let ast = if matches!(self.kind, SmtKind::Bitvec { signed, .. } if signed) {
            unsafe { Z3_mk_bvslt(self.ctxt.ctxt, self.ast, rhs.ast) }
        } else {
            unsafe { Z3_mk_bvult(self.ctxt.ctxt, self.ast, rhs.ast) }
        };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bool,
        }
    }

    // equality operator (for both bool and bitvec)
    pub fn eq(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op(rhs);
        let ast = unsafe { Z3_mk_eq(self.ctxt.ctxt, self.ast, rhs.ast) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bool,
        }
    }

    pub fn ne(&self, rhs: &SmtExpr<'a>) -> SmtExpr<'a> {
        self.check_binary_op_bool(rhs);
        let terms: [Z3_ast; 2] = [self.ast, rhs.ast];
        let ast = unsafe { Z3_mk_distinct(self.ctxt.ctxt, 2, terms.as_ptr()) };
        SmtExpr {
            ast,
            ctxt: self.ctxt,
            kind: SmtKind::Bool,
        }
    }
}
