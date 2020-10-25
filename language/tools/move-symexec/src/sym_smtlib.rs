// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{ffi::CString, os::raw::c_uint};

use crate::deps_z3::*;

/// A wrapper over Z3_context
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
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, Z3_mk_bool_sort(self.ctxt))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind: SmtKind::Bool,
        }
    }

    // create bitvecs
    fn bitvec_const<T: ToString>(&self, val: T, signed: bool, width: u16) -> SmtExpr {
        let str_repr = CString::new(val.to_string()).unwrap();
        let ast = unsafe {
            Z3_mk_numeral(
                self.ctxt,
                str_repr.as_ptr(),
                Z3_mk_bv_sort(self.ctxt, width as c_uint),
            )
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind: SmtKind::Bitvec { signed, width },
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
        let c_str = CString::new(var).unwrap();
        let ast = unsafe {
            let symbol = Z3_mk_string_symbol(self.ctxt, c_str.as_ptr());
            Z3_mk_const(self.ctxt, symbol, Z3_mk_bv_sort(self.ctxt, width as c_uint))
        };
        SmtExpr {
            ast,
            ctxt: self,
            kind: SmtKind::Bitvec { signed, width },
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
}

impl Drop for SmtCtxt {
    fn drop(&mut self) {
        unsafe {
            Z3_del_context(self.ctxt);
        }
    }
}

/// Make the type of SmtExpr explicit
enum SmtKind {
    Bool,
    Bitvec { signed: bool, width: u16 },
}

/// A wrapper over Z3_ast
pub(crate) struct SmtExpr<'a> {
    ast: Z3_ast,
    ctxt: &'a SmtCtxt,
    kind: SmtKind,
}
