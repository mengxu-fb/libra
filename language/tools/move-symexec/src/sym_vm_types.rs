// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use itertools::Itertools;

use move_core_types::{
    account_address::AccountAddress, parser::parse_transaction_argument,
    transaction_argument::TransactionArgument,
};
use vm::file_format::SignatureToken;

use crate::sym_smtlib::{SmtCtxt, SmtExpr, SmtKind, SmtResult};

/// Guarded symbolic representation. Each symboilc expression is guarded
/// by a condition over the variables.
struct SymRepr<'a> {
    expr: SmtExpr<'a>,
    cond: SmtExpr<'a>,
}

/// A symbolic mimic of the move_vm_types::values::Value.
pub struct SymValue<'a> {
    /// A reference to the smt context
    ctxt: &'a SmtCtxt,
    /// A collection of guarded expressions describing all possibilities
    /// (i.e., all variants) this value may take as well as all the
    /// conditions associated with each variant.
    variants: Vec<SymRepr<'a>>,
}
// TODO: make SymValue pub(crate)

macro_rules! make_sym_primitive {
    ($ctxt:ident, $v:ident, $func:tt $(,$extra:ident)*) => {
        SymValue {
            ctxt: $ctxt,
            variants: vec![SymRepr {
                expr: $ctxt.$func($($extra,)* $v),
                cond: $ctxt.bool_const(true),
            }],
        }
    };
}

macro_rules! make_sym_from_arg {
    ($kind:tt, $ctxt:ident, $arg:ident, $func_const:tt, $func_var:tt) => {
        match $arg {
            SymTransactionArgument::Concrete(c_arg) => {
                if let TransactionArgument::$kind(val) = c_arg {
                    SymValue::$func_const($ctxt, val.clone())
                } else {
                    panic!("Mismatched types in symbolic argument");
                }
            }
            SymTransactionArgument::Symbolic(var) => SymValue::$func_var($ctxt, var),
        }
    };
}

macro_rules! sym_op_unary {
    ($func:tt, $sym:ident) => {{
        SymValue::op($sym.ctxt, &[$sym], |parts| {
            debug_assert_eq!(parts.len(), 1);
            parts[0].$func()
        })
    }};
}

macro_rules! sym_op_binary {
    ($func:tt, $lhs:ident, $rhs:ident) => {{
        SymValue::op($lhs.ctxt, &[$lhs, $rhs], |parts| {
            debug_assert_eq!(parts.len(), 2);
            parts[0].$func(parts[1])
        })
    }};
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

    // create address
    pub fn address_const(ctxt: &'a SmtCtxt, val: AccountAddress) -> Self {
        make_sym_primitive!(ctxt, val, address_const)
    }

    pub fn address_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        make_sym_primitive!(ctxt, var, address_var)
    }

    // create vector
    pub fn vector_const(ctxt: &'a SmtCtxt, element_kind: &SmtKind, vals: &[&SymValue<'a>]) -> Self {
        SymValue::op(ctxt, vals, |exprs| ctxt.vector_const(element_kind, exprs))
    }

    pub fn vector_var(ctxt: &'a SmtCtxt, element_kind: &SmtKind, var: &str) -> Self {
        make_sym_primitive!(ctxt, var, vector_var, element_kind)
    }

    // create vector (utilities)
    fn vector_u8_const(ctxt: &'a SmtCtxt, vals: Vec<u8>) -> Self {
        let elements: Vec<SymValue> = vals
            .iter()
            .map(|val| SymValue::u8_const(ctxt, *val))
            .collect();
        let element_refs: Vec<&SymValue> = elements.iter().collect();
        SymValue::vector_const(ctxt, &SmtKind::bitvec_u8(), &element_refs)
    }

    fn vector_u8_var(ctxt: &'a SmtCtxt, var: &str) -> Self {
        SymValue::vector_var(ctxt, &SmtKind::bitvec_u8(), var)
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

    fn address_arg(ctxt: &'a SmtCtxt, arg: &SymTransactionArgument) -> Self {
        make_sym_from_arg!(Address, ctxt, arg, address_const, address_var)
    }

    fn vector_u8_arg(ctxt: &'a SmtCtxt, arg: &SymTransactionArgument) -> Self {
        make_sym_from_arg!(U8Vector, ctxt, arg, vector_u8_const, vector_u8_var)
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
            SignatureToken::Address | SignatureToken::Signer => SymValue::address_arg(ctxt, arg),
            SignatureToken::Vector(element) => {
                // the only supported vector element type from
                // TransactionArgument is U8Vector, hence the assert.
                debug_assert_eq!(**element, SignatureToken::U8);
                SymValue::vector_u8_arg(ctxt, arg)
            }
            _ => panic!("Invalid signature type for value argument"),
        }
    }

    // operations
    fn op<F>(ctxt: &'a SmtCtxt, operands: &[&SymValue<'a>], func: F) -> Self
    where
        F: Fn(&[&SmtExpr<'a>]) -> SmtExpr<'a>,
    {
        // check consistency of ctxt
        debug_assert!(operands.iter().all(|sym| ctxt.smt_ctxt_matches(sym.ctxt)));

        // variants for the result
        let mut variants: Vec<SymRepr<'a>> = vec![];

        // get the cartesian product of all operands
        let prod = operands
            .iter()
            .map(|sym| sym.variants.iter())
            .multi_cartesian_product();

        // iterate over all possible combinations
        for combo in prod {
            // derive new condition
            let cond = combo
                .iter()
                .fold(ctxt.bool_const(true), |acc, variant| acc.and(&variant.cond));

            // check feasibility
            let feasible = match ctxt.solve(&[&cond]) {
                SmtResult::SAT => true,
                SmtResult::UNSAT => false,
                SmtResult::UNKNOWN => {
                    // TODO: assume that things are decidable for now
                    panic!("SMT solver returns an unknown result");
                }
            };

            if !feasible {
                continue;
            }

            // derive the new expression
            let parts: Vec<&SmtExpr> = combo.iter().map(|variant| &variant.expr).collect();
            let expr = (func)(&parts);

            // check duplicates
            let dup = variants.iter_mut().find(|repr| {
                match ctxt.solve(&[&repr.expr.ne(&expr)]) {
                    SmtResult::SAT => false,
                    SmtResult::UNSAT => true,
                    SmtResult::UNKNOWN => {
                        // TODO: assume that things are decidable for now
                        panic!("SMT solver returns an unknown result");
                    }
                }
            });

            if let Some(item) = dup {
                // join the conditions
                item.cond = item.cond.or(&cond);
            } else {
                // add a new variant
                variants.push(SymRepr { expr, cond });
            }
        }

        // done
        Self { ctxt, variants }
    }

    // bool operations
    pub fn not(&self) -> SymValue<'a> {
        sym_op_unary!(not, self)
    }

    pub fn and(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(and, self, rhs)
    }

    pub fn or(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(or, self, rhs)
    }

    // bitvec operations
    pub fn add(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(add, self, rhs)
    }

    pub fn sub(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(sub, self, rhs)
    }

    pub fn mul(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(mul, self, rhs)
    }

    pub fn div(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(div, self, rhs)
    }

    pub fn rem(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(rem, self, rhs)
    }

    pub fn cast_u8(&self) -> SymValue<'a> {
        sym_op_unary!(cast_u8, self)
    }

    pub fn cast_u64(&self) -> SymValue<'a> {
        sym_op_unary!(cast_u64, self)
    }

    pub fn cast_u128(&self) -> SymValue<'a> {
        sym_op_unary!(cast_u128, self)
    }

    pub fn bit_and(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(bit_and, self, rhs)
    }

    pub fn bit_or(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(bit_or, self, rhs)
    }

    pub fn bit_xor(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(bit_xor, self, rhs)
    }

    pub fn shl(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(shl, self, rhs)
    }

    pub fn shr(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(shr, self, rhs)
    }

    pub fn gt(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(gt, self, rhs)
    }

    pub fn ge(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(ge, self, rhs)
    }

    pub fn le(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(le, self, rhs)
    }

    pub fn lt(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(lt, self, rhs)
    }

    // generic operations
    pub fn eq(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(eq, self, rhs)
    }

    pub fn ne(&self, rhs: &SymValue<'a>) -> SymValue<'a> {
        sym_op_binary!(ne, self, rhs)
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

/// A symbolic version of the struct used in concrete execution
/// [Locals] (move_vm_types::values::Locals)
pub(crate) struct SymLocals<'a> {
    _slots: Vec<Option<&'a SymValue<'a>>>,
}

impl<'a> SymLocals<'a> {
    pub fn new(size: usize, args: &'a [SymValue]) -> Self {
        let mut slots = Vec::with_capacity(size);
        for sym in args {
            slots.push(Some(sym));
        }
        for _ in 0..(size - args.len()) {
            slots.push(None);
        }
        Self { _slots: slots }
    }
}
