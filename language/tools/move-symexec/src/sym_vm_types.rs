// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};

use move_core_types::{
    parser::parse_transaction_argument, transaction_argument::TransactionArgument,
};

use crate::sym_smtlib::{SmtCtxt, SmtExpr};

/// Guarded symbolic representation. Each symboilc expression is guarded
/// by a condition over the variables.
struct SymVariant<'a> {
    expr: SmtExpr<'a>,
    cond: SmtExpr<'a>,
}

/// A collection of guarded expressions describing all possibilities
/// (i.e., variants) this value may take as well as all the condition
/// associated with each variant.
pub(crate) struct SymRepr<'a> {
    variants: Vec<SymVariant<'a>>,
}

/// A symbolic mimic of the move_vm_types::values::Value.
pub(crate) enum SymValue<'a> {
    Invalid,

    Bool { repr: SymRepr<'a> },

    U8 { repr: SymRepr<'a> },
    U64 { repr: SymRepr<'a> },
    U128 { repr: SymRepr<'a> },
    // TODO: more to be added
}

macro_rules! make_sym {
    ($kind:tt, $ctxt:ident, $v:ident, $func:tt) => {
        SymValue::$kind {
            repr: SymRepr {
                variants: vec![SymVariant {
                    expr: $ctxt.$func($v),
                    cond: $ctxt.bool_const(true),
                }],
            },
        }
    };
}

impl<'a> SymValue<'a> {
    // create bool
    pub fn bool_const(ctxt: &'a SmtCtxt, val: bool) -> Self {
        make_sym!(Bool, ctxt, val, bool_const)
    }

    pub fn bool_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym!(Bool, ctxt, var, bool_var)
    }

    // create bitvec
    pub fn u8_const(ctxt: &'a SmtCtxt, val: u8) -> Self {
        make_sym!(U8, ctxt, val, bitvec_const_u8)
    }

    pub fn u64_const(ctxt: &'a SmtCtxt, val: u64) -> Self {
        make_sym!(U64, ctxt, val, bitvec_const_u64)
    }

    pub fn u128_const(ctxt: &'a SmtCtxt, val: u128) -> Self {
        make_sym!(U128, ctxt, val, bitvec_const_u128)
    }

    pub fn u8_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym!(U8, ctxt, var, bitvec_var_u8)
    }

    pub fn u64_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym!(U64, ctxt, var, bitvec_var_u64)
    }

    pub fn u128_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym!(U128, ctxt, var, bitvec_var_u128)
    }
}

/// A holder for arguments that could be either symbolic or concrete
pub enum SymTransactionArgument {
    Concrete(TransactionArgument),
    Symbolic(String),
}

/// A utility parser that convert strings to symbolic argumnent
pub(crate) fn parse_sym_transaction_argument(s: &str) -> Result<SymTransactionArgument> {
    let tokens: Vec<&str> = s.split("::").collect();
    if tokens.len() != 2 {
        bail!("Invalid symbolic transaction argument");
    };

    if tokens[0] == "C" {
        Ok(SymTransactionArgument::Concrete(
            parse_transaction_argument(tokens[1])?,
        ))
    } else if tokens[0] == "S" {
        Ok(SymTransactionArgument::Symbolic(tokens[1].to_owned()))
    } else {
        bail!("Invalid symbolic transaction argument");
    }
}
