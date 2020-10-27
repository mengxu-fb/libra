// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use itertools::Itertools;

use move_core_types::{
    parser::parse_transaction_argument, transaction_argument::TransactionArgument,
};
use vm::file_format::SignatureToken;

use crate::sym_smtlib::{SmtCtxt, SmtExpr, SmtKind, SmtResult};

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
pub(crate) struct SymValue<'a> {
    repr: SymRepr<'a>,
}

macro_rules! make_sym_primitive {
    ($ctxt:ident, $v:ident, $func:tt) => {
        SymValue {
            repr: SymRepr {
                variants: vec![SymVariant {
                    expr: $ctxt.$func($v),
                    cond: $ctxt.bool_const(true),
                }],
            },
        }
    };
}

macro_rules! make_sym_from_arg {
    ($kind:tt, $ctxt:ident, $arg:ident, $func_const:tt, $func_var:tt) => {
        match $arg {
            SymTransactionArgument::Concrete(c_arg) => {
                if let TransactionArgument::$kind(val) = c_arg {
                    SymValue::$func_const($ctxt, *val)
                } else {
                    panic!("Mismatched types in symbolic argument");
                }
            }
            SymTransactionArgument::Symbolic(var) => SymValue::$func_var($ctxt, var),
        }
    };
}

impl<'a> SymValue<'a> {
    // create bool
    pub fn bool_const(ctxt: &'a SmtCtxt, val: bool) -> Self {
        make_sym_primitive!(ctxt, val, bool_const)
    }

    pub fn bool_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym_primitive!(ctxt, var, bool_var)
    }

    // create bitvec
    pub fn u8_const(ctxt: &'a SmtCtxt, val: u8) -> Self {
        make_sym_primitive!(ctxt, val, bitvec_const_u8)
    }

    pub fn u64_const(ctxt: &'a SmtCtxt, val: u64) -> Self {
        make_sym_primitive!(ctxt, val, bitvec_const_u64)
    }

    pub fn u128_const(ctxt: &'a SmtCtxt, val: u128) -> Self {
        make_sym_primitive!(ctxt, val, bitvec_const_u128)
    }

    pub fn u8_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym_primitive!(ctxt, var, bitvec_var_u8)
    }

    pub fn u64_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym_primitive!(ctxt, var, bitvec_var_u64)
    }

    pub fn u128_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym_primitive!(ctxt, var, bitvec_var_u128)
    }

    // create from argument
    fn bool_arg(ctxt: &'a SmtCtxt, arg: &SymTransactionArgument) -> Self {
        make_sym_from_arg!(Bool, ctxt, arg, bool_const, bool_var)
    }

    fn u8_arg(ctxt: &'a SmtCtxt, arg: &SymTransactionArgument) -> Self {
        make_sym_from_arg!(U8, ctxt, arg, u8_const, u8_var)
    }

    fn u64_arg(ctxt: &'a SmtCtxt, arg: &SymTransactionArgument) -> Self {
        make_sym_from_arg!(U64, ctxt, arg, u64_const, u64_var)
    }

    fn u128_arg(ctxt: &'a SmtCtxt, arg: &SymTransactionArgument) -> Self {
        make_sym_from_arg!(U128, ctxt, arg, u128_const, u128_var)
    }

    pub fn from_transaction_argument(
        ctxt: &'a SmtCtxt,
        sig: &SignatureToken,
        arg: &SymTransactionArgument,
    ) -> Self {
        match sig {
            SignatureToken::Bool => SymValue::bool_arg(ctxt, arg),
            SignatureToken::U8 => SymValue::u8_arg(ctxt, arg),
            SignatureToken::U64 => SymValue::u64_arg(ctxt, arg),
            SignatureToken::U128 => SymValue::u128_arg(ctxt, arg),
            _ => panic!("Not supported yet"), // TODO
        }
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
