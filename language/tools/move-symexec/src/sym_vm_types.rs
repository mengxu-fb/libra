// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use itertools::Itertools;
use log::debug;
use once_cell::sync::Lazy;
use std::{collections::BTreeMap, fmt};

use bytecode::stackless_bytecode::TempIndex;
use move_core_types::{
    account_address::AccountAddress, parser::parse_transaction_argument,
    transaction_argument::TransactionArgument,
};
use spec_lang::ty::{PrimitiveType, Type};

use crate::sym_smtlib::{SmtCtxt, SmtExpr, SmtKind};

// Move first class citizen: Address
const ADDRESS_STRUCT_NAME: &str = "-Address-";
const ADDRESS_STRUCT_VALUE_FIELD_NAME: &str = "value";
const ADDRESS_STRUCT_VALUE_FIELD_BITVEC_WIDTH: u16 = 128;
pub(crate) static ADDRESS_SMT_KIND: Lazy<SmtKind> = Lazy::new(|| SmtKind::Struct {
    struct_name: ADDRESS_STRUCT_NAME.to_owned(),
});

// Move first class citizen: Signer
const SIGNER_STRUCT_NAME: &str = "-Signer-";
const SIGNER_STRUCT_ADDRESS_FIELD_NAME: &str = "address";
pub(crate) static SIGNER_SMT_KIND: Lazy<SmtKind> = Lazy::new(|| SmtKind::Struct {
    struct_name: SIGNER_STRUCT_NAME.to_owned(),
});

// Preparation for move first class citizen types
impl SmtCtxt {
    pub(crate) fn create_move_type_address(&mut self) {
        self.create_smt_struct(
            ADDRESS_STRUCT_NAME.to_owned(),
            vec![(
                ADDRESS_STRUCT_VALUE_FIELD_NAME.to_owned(),
                SmtKind::Bitvec {
                    signed: false,
                    width: ADDRESS_STRUCT_VALUE_FIELD_BITVEC_WIDTH,
                },
            )],
        );
    }

    pub(crate) fn create_move_type_signer(&mut self) {
        self.create_smt_struct(
            SIGNER_STRUCT_NAME.to_owned(),
            vec![(
                SIGNER_STRUCT_ADDRESS_FIELD_NAME.to_owned(),
                ADDRESS_SMT_KIND.clone(),
            )],
        );
    }
}

/// Guarded symbolic representation: each symboilc expression is guarded by a condition
#[derive(Clone, Debug)]
struct SymRepr<'smt> {
    expr: SmtExpr<'smt>,
    cond: SmtExpr<'smt>,
}

impl fmt::Display for SymRepr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} | {}", self.expr, self.cond)
    }
}

/// A symbolic mimic of the `move_vm_types::values::Value`
#[derive(Clone, Debug)]
pub struct SymValue<'smt> {
    /// A reference to the smt context
    ctxt: &'smt SmtCtxt,
    /// A collection of guarded expressions describing all possibilities (i.e., all variants) this
    /// value may take as well as the conditions associated with each variant.
    variants: Vec<SymRepr<'smt>>,
}

impl fmt::Display for SymValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[")?;
        for (i, variant) in self.variants.iter().enumerate() {
            writeln!(f, "\t{}: {}", i, variant)?;
        }
        writeln!(f, "]")?;
        Ok(())
    }
}

impl<'smt> SymValue<'smt> {
    pub fn flatten_as_predicate(&self, pred: bool) -> SmtExpr<'smt> {
        if self.variants.is_empty() {
            // if there is no variants, it means that there is no way to set this symbolic value
            self.ctxt.bool_const(false)
        } else {
            self.variants
                .iter()
                .fold(self.ctxt.bool_const(false), |acc, repr| {
                    let clause = if pred {
                        repr.expr.and(&repr.cond)
                    } else {
                        repr.expr.not().and(&repr.cond)
                    };
                    acc.or(&clause)
                })
        }
    }
}
// TODO: make SymValue pub(crate)

macro_rules! make_sym_primitive {
    ($ctxt:ident, $cond:ident, $func:tt, $arg0:ident $(,$args:ident)*) => {
        Ok(SymValue {
            ctxt: $ctxt,
            variants: vec![SymRepr {
                expr: $ctxt.$func($arg0, $($args,)*),
                cond: $cond.clone(),
            }],
        })
    };
}

macro_rules! make_sym_from_arg {
    ($kind:tt, $ctxt:ident, $arg:ident, $func_const:tt, $func_var:tt) => {
        match $arg {
            SymTransactionArgument::Concrete(c_arg) => {
                if let TransactionArgument::$kind(val) = c_arg {
                    SymValue::$func_const($ctxt, val.clone(), &$ctxt.bool_const(true))
                } else {
                    panic!("Mismatched types in symbolic argument");
                }
            }
            SymTransactionArgument::Symbolic(var) => {
                SymValue::$func_var($ctxt, var, &$ctxt.bool_const(true))
            }
        }
    };
}

macro_rules! sym_op_unary {
    ($func:tt, $sym:ident, $cond:ident $(,$args:ident)*) => {{
        SymValue::op(
            $sym.ctxt,
            &[$sym],
            |parts| {
                debug_assert_eq!(parts.len(), 1);
                parts[0].$func($($args,)*)
            },
            $cond,
        )
    }};
}

macro_rules! sym_op_binary {
    ($func:tt, $lhs:ident, $rhs:ident, $cond:ident $(,$args:ident)*) => {{
        SymValue::op(
            $lhs.ctxt,
            &[$lhs, $rhs],
            |parts| {
                debug_assert_eq!(parts.len(), 2);
                parts[0].$func(parts[1], $($args,)*)
            },
            $cond,
        )
    }};
}

impl<'smt> SymValue<'smt> {
    // create bool
    pub fn bool_const(ctxt: &'smt SmtCtxt, val: bool, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bool_const, val)
    }

    pub fn bool_var(ctxt: &'smt SmtCtxt, var: &str, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bool_var, var)
    }

    // create bitvec
    fn uint_const<T: ToString>(
        ctxt: &'smt SmtCtxt,
        val: T,
        width: u16,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_const, val, false, width)
    }

    pub fn u8_const(ctxt: &'smt SmtCtxt, val: u8, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_const_u8, val)
    }

    pub fn u64_const(ctxt: &'smt SmtCtxt, val: u64, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_const_u64, val)
    }

    pub fn u128_const(ctxt: &'smt SmtCtxt, val: u128, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_const_u128, val)
    }

    pub fn u8_var(ctxt: &'smt SmtCtxt, var: &str, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_var_u8, var)
    }

    pub fn u64_var(ctxt: &'smt SmtCtxt, var: &str, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_var_u64, var)
    }

    pub fn u128_var(ctxt: &'smt SmtCtxt, var: &str, cond: &SmtExpr<'smt>) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, bitvec_var_u128, var)
    }

    // create vector
    pub fn vector_const(
        ctxt: &'smt SmtCtxt,
        element_kind: &SmtKind,
        vals: &[&SymValue<'smt>],
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        SymValue::op(
            ctxt,
            vals,
            |exprs| ctxt.vector_const(element_kind, exprs),
            cond,
        )
    }

    pub fn vector_var(
        ctxt: &'smt SmtCtxt,
        element_kind: &SmtKind,
        var: &str,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, vector_var, element_kind, var)
    }

    // create vector (utilities)
    pub fn vector_u8_const(
        ctxt: &'smt SmtCtxt,
        vals: Vec<u8>,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        let elements = vals
            .iter()
            .map(|val| SymValue::u8_const(ctxt, *val, cond))
            .collect::<Result<Vec<_>>>()?;
        let element_refs: Vec<&SymValue> = elements.iter().collect();
        SymValue::vector_const(ctxt, &SmtKind::bitvec_u8(), &element_refs, cond)
    }

    fn vector_u8_var(ctxt: &'smt SmtCtxt, var: &str, cond: &SmtExpr<'smt>) -> Result<Self> {
        SymValue::vector_var(ctxt, &SmtKind::bitvec_u8(), var, cond)
    }

    // create struct
    pub fn struct_const(
        ctxt: &'smt SmtCtxt,
        struct_kind: &SmtKind,
        fields: &[&SymValue<'smt>],
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        SymValue::op(
            ctxt,
            fields,
            |exprs| ctxt.struct_const(struct_kind, exprs),
            cond,
        )
    }

    pub fn struct_var(
        ctxt: &'smt SmtCtxt,
        struct_kind: &SmtKind,
        var: &str,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        make_sym_primitive!(ctxt, cond, struct_var, struct_kind, var)
    }

    // create address
    pub fn address_const(
        ctxt: &'smt SmtCtxt,
        val: AccountAddress,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        Self::struct_const(
            ctxt,
            &*ADDRESS_SMT_KIND,
            &[&SymValue::uint_const(
                ctxt,
                addr_to_uint(&val),
                ADDRESS_STRUCT_VALUE_FIELD_BITVEC_WIDTH,
                &ctxt.bool_const(true),
            )?],
            cond,
        )
    }

    pub fn address_var(ctxt: &'smt SmtCtxt, var: &str, cond: &SmtExpr<'smt>) -> Result<Self> {
        Self::struct_var(ctxt, &*ADDRESS_SMT_KIND, var, cond)
    }

    // create signers
    pub fn signer_const(
        ctxt: &'smt SmtCtxt,
        val: AccountAddress,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        Self::struct_const(
            ctxt,
            &*SIGNER_SMT_KIND,
            &[&SymValue::address_const(ctxt, val, &ctxt.bool_const(true))?],
            cond,
        )
    }

    // create from argument
    fn bool_arg(ctxt: &'smt SmtCtxt, arg: &SymTransactionArgument) -> Result<Self> {
        make_sym_from_arg!(Bool, ctxt, arg, bool_const, bool_var)
    }

    fn u8_arg(ctxt: &'smt SmtCtxt, arg: &SymTransactionArgument) -> Result<Self> {
        make_sym_from_arg!(U8, ctxt, arg, u8_const, u8_var)
    }

    fn u64_arg(ctxt: &'smt SmtCtxt, arg: &SymTransactionArgument) -> Result<Self> {
        make_sym_from_arg!(U64, ctxt, arg, u64_const, u64_var)
    }

    fn u128_arg(ctxt: &'smt SmtCtxt, arg: &SymTransactionArgument) -> Result<Self> {
        make_sym_from_arg!(U128, ctxt, arg, u128_const, u128_var)
    }

    fn address_arg(ctxt: &'smt SmtCtxt, arg: &SymTransactionArgument) -> Result<Self> {
        make_sym_from_arg!(Address, ctxt, arg, address_const, address_var)
    }

    fn vector_u8_arg(ctxt: &'smt SmtCtxt, arg: &SymTransactionArgument) -> Result<Self> {
        make_sym_from_arg!(U8Vector, ctxt, arg, vector_u8_const, vector_u8_var)
    }

    pub fn from_transaction_argument(
        ctxt: &'smt SmtCtxt,
        sig: &Type,
        arg: &SymTransactionArgument,
    ) -> Result<Self> {
        match sig {
            Type::Primitive(primitive) => match primitive {
                PrimitiveType::Bool => SymValue::bool_arg(ctxt, arg),
                PrimitiveType::U8 => SymValue::u8_arg(ctxt, arg),
                PrimitiveType::U64 => SymValue::u64_arg(ctxt, arg),
                PrimitiveType::U128 => SymValue::u128_arg(ctxt, arg),
                PrimitiveType::Address => SymValue::address_arg(ctxt, arg),
                _ => panic!("Unexpected type for transaction argument {:?}", primitive),
            },
            Type::Vector(element_type) => {
                // the only supported vector element type from TransactionArgument is Vector<u8>
                debug_assert_eq!(**element_type, Type::Primitive(PrimitiveType::U8));
                SymValue::vector_u8_arg(ctxt, arg)
            }
            _ => panic!("Invalid type for transaction argument"),
        }
    }

    // operations
    fn op<F>(
        ctxt: &'smt SmtCtxt,
        operands: &[&SymValue<'smt>],
        func: F,
        base_cond: &SmtExpr<'smt>,
    ) -> Result<Self>
    where
        F: Fn(&[&SmtExpr<'smt>]) -> SmtExpr<'smt>,
    {
        // check consistency of ctxt
        debug_assert!(operands.iter().all(|sym| ctxt.smt_ctxt_matches(sym.ctxt)));

        // variants for the result
        let mut variants: Vec<SymRepr<'smt>> = vec![];

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
                .fold(base_cond.clone(), |acc, variant| acc.and(&variant.cond));

            // check feasibility
            if !ctxt.is_feasible_assume_solvable(&[&cond])? {
                continue;
            }

            // derive the new expression
            let parts: Vec<&SmtExpr> = combo.iter().map(|variant| &variant.expr).collect();
            let expr = (func)(&parts);

            // check duplicates
            let mut dup = None;
            for repr in variants.iter_mut() {
                if !ctxt.is_feasible_assume_solvable(&[&repr.expr.ne(&expr)])? {
                    dup = Some(repr);
                }
            }

            if let Some(item) = dup {
                // join the conditions
                item.cond = item.cond.or(&cond);
            } else {
                // add a new variant
                variants.push(SymRepr { expr, cond });
            }
        }

        // done
        Ok(Self { ctxt, variants })
    }

    // bool operations
    pub fn not(&self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_unary!(not, self, cond)
    }

    pub fn and(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(and, self, rhs, cond)
    }

    pub fn or(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(or, self, rhs, cond)
    }

    // bitvec operations
    pub fn add(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(add, self, rhs, cond)
    }

    pub fn sub(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(sub, self, rhs, cond)
    }

    pub fn mul(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(mul, self, rhs, cond)
    }

    pub fn div(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(div, self, rhs, cond)
    }

    pub fn rem(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(rem, self, rhs, cond)
    }

    pub fn cast_u8(&self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_unary!(cast_u8, self, cond)
    }

    pub fn cast_u64(&self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_unary!(cast_u64, self, cond)
    }

    pub fn cast_u128(&self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_unary!(cast_u128, self, cond)
    }

    pub fn bit_and(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(bit_and, self, rhs, cond)
    }

    pub fn bit_or(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(bit_or, self, rhs, cond)
    }

    pub fn bit_xor(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(bit_xor, self, rhs, cond)
    }

    pub fn shl(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(shl, self, rhs, cond)
    }

    pub fn shr(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(shr, self, rhs, cond)
    }

    pub fn gt(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(gt, self, rhs, cond)
    }

    pub fn ge(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(ge, self, rhs, cond)
    }

    pub fn le(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(le, self, rhs, cond)
    }

    pub fn lt(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(lt, self, rhs, cond)
    }

    // struct operations
    pub fn get_field(&self, field_num: usize, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_unary!(get_field, self, cond, field_num)
    }

    pub fn put_field(
        &self,
        field_sym: &Self,
        field_num: usize,
        cond: &SmtExpr<'smt>,
    ) -> Result<Self> {
        sym_op_binary!(put_field, self, field_sym, cond, field_num)
    }

    pub fn unpack(&self, num_fields: usize, base_cond: &SmtExpr<'smt>) -> Result<Vec<Self>> {
        let ctxt = self.ctxt;

        // initialize the unpacked fields
        let mut results = Vec::new();
        for _ in 0..num_fields {
            results.push(SymValue {
                ctxt: self.ctxt,
                variants: vec![],
            });
        }

        // add options to each field
        for repr in &self.variants {
            let cond = base_cond.and(&repr.cond);

            let unpacked_exprs = repr.expr.unpack();
            debug_assert_eq!(unpacked_exprs.len(), num_fields);

            for (i, expr) in unpacked_exprs.iter().enumerate() {
                // get the target value
                let field_sym = results.get_mut(i).unwrap();

                // check duplicates
                let mut dup = None;
                for repr in field_sym.variants.iter_mut() {
                    if !ctxt.is_feasible_assume_solvable(&[&repr.expr.ne(&expr)])? {
                        dup = Some(repr);
                    }
                }

                if let Some(item) = dup {
                    // join the conditions
                    item.cond = item.cond.or(&cond);
                } else {
                    // add a new variant
                    field_sym.variants.push(SymRepr {
                        expr: expr.clone(),
                        cond: cond.clone(),
                    });
                }
            }
        }

        // done
        Ok(results)
    }

    // generic operations
    pub fn eq(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(eq, self, rhs, cond)
    }

    pub fn ne(&self, rhs: &Self, cond: &SmtExpr<'smt>) -> Result<Self> {
        sym_op_binary!(ne, self, rhs, cond)
    }
}

/// A holder for arguments that could be either symbolic or concrete
pub enum SymTransactionArgument {
    Concrete(TransactionArgument),
    Symbolic(String),
}

/// A utility parser that convert strings to symbolic argument
pub fn parse_sym_transaction_argument(s: &str) -> Result<SymTransactionArgument> {
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

/// A symbolic memory slot that tracks not only the symbolic value, but also the liveliness
/// condition (i.e., the condition on which the symbolic value is valid when the slot is loaded)
struct SymMemSlot<'smt> {
    expr: SmtExpr<'smt>,
    cond: SmtExpr<'smt>,
}

impl fmt::Display for SymMemSlot<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} | {}", self.expr, self.cond)
    }
}

/// A symbolic version for cells that serve the purpose of memory
struct SymMemCell<'smt> {
    /// A reference to the smt context
    ctxt: &'smt SmtCtxt,
    /// Possible slots
    slots: Vec<SymMemSlot<'smt>>,
}

impl fmt::Display for SymMemCell<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[")?;
        for (i, slot) in self.slots.iter().enumerate() {
            writeln!(f, "\t{}: {}", i, slot)?;
        }
        writeln!(f, "]")?;
        Ok(())
    }
}

impl<'smt> SymMemCell<'smt> {
    fn new(ctxt: &'smt SmtCtxt) -> Self {
        Self {
            ctxt,
            slots: vec![],
        }
    }

    fn store(&mut self, sym: &SymValue<'smt>, cond: &SmtExpr<'smt>) -> Result<()> {
        let ctxt = self.ctxt;

        // collect newly added slots
        let mut new_slots = vec![];
        for variant in &sym.variants {
            // filter infeasible read
            let new_slot_cond = variant.cond.and(cond);
            if !ctxt.is_feasible_assume_solvable(&[&new_slot_cond])? {
                continue;
            }

            // update liveliness conditions for existing records
            for slot in self.slots.iter_mut() {
                slot.cond = slot.cond.and(&new_slot_cond.not());
            }

            // add a new slot
            new_slots.push(SymMemSlot {
                expr: variant.expr.clone(),
                cond: new_slot_cond,
            });
        }

        // remove dead records
        let mut del_slots = vec![];
        for (i, slot) in self.slots.iter().enumerate() {
            if !ctxt.is_feasible_assume_solvable(&[&slot.cond])? {
                del_slots.push(i);
            }
        }
        for (i, slot_index) in del_slots.into_iter().enumerate() {
            self.slots.remove(slot_index - i);
        }

        // add newly created slots
        self.slots.append(&mut new_slots);

        // done
        Ok(())
    }

    fn load(&mut self, cond: &SmtExpr<'smt>, extract: bool) -> Result<SymValue<'smt>> {
        let ctxt = self.ctxt;
        let mut variants = vec![];

        // see which slot(s) are still alive given the condition
        let mut del_slots = vec![];
        for (i, slot) in self.slots.iter().enumerate() {
            let repr_cond = slot.cond.and(cond);

            // filter infeasible slots
            if !ctxt.is_feasible_assume_solvable(&[&repr_cond])? {
                continue;
            }

            del_slots.push(i);
            variants.push(SymRepr {
                expr: slot.expr.clone(),
                cond: repr_cond,
            });
        }

        // remove extracted slots (if needed)
        if extract {
            for (offset, slot_index) in del_slots.into_iter().enumerate() {
                self.slots.remove(slot_index - offset);
            }
        }

        // done
        Ok(SymValue {
            ctxt: self.ctxt,
            variants,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SymRefType {
    Local {
        slot_index: TempIndex,
    },
    Field {
        slot_index: TempIndex,
        field_num: usize,
    },
}

impl fmt::Display for SymRefType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymRefType::Local { slot_index } => write!(f, "Local({})", slot_index),
            SymRefType::Field {
                slot_index,
                field_num,
            } => write!(f, "Field({}, {})", slot_index, field_num),
        }
    }
}

/// A symbolic reference slot that tracks not only the referred value, but also
/// the liveliness condition (i.e., the condition on which the referred value is
/// valid to guide the slot write-back)
struct SymRefSlot<'smt> {
    refv: SymRefType,
    cond: SmtExpr<'smt>,
}

impl fmt::Display for SymRefSlot<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} | {}", self.refv, self.cond)
    }
}

/// A symbolic version for cells that serve the purpose of reference pointers
struct SymRefCell<'smt> {
    /// A reference to the smt context
    ctxt: &'smt SmtCtxt,
    /// Possible slots
    slots: Vec<SymRefSlot<'smt>>,
}

impl fmt::Display for SymRefCell<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[")?;
        for (i, slot) in self.slots.iter().enumerate() {
            writeln!(f, "\t{}: {}", i, slot)?;
        }
        writeln!(f, "]")?;
        Ok(())
    }
}

impl<'smt> SymRefCell<'smt> {
    fn new(ctxt: &'smt SmtCtxt) -> Self {
        Self {
            ctxt,
            slots: vec![],
        }
    }

    fn record(&mut self, rty: &SymRefType, cond: &SmtExpr<'smt>) -> Result<()> {
        let ctxt = self.ctxt;

        // check overlaps
        for slot in self.slots.iter_mut() {
            slot.cond = slot.cond.and(&cond.not());
        }
        let new_slot = SymRefSlot {
            refv: rty.clone(),
            cond: cond.clone(),
        };

        // remove dead records
        let mut del_slots = vec![];
        for (i, slot) in self.slots.iter().enumerate() {
            if !ctxt.is_feasible_assume_solvable(&[&slot.cond])? {
                del_slots.push(i);
            }
        }
        for (i, slot_index) in del_slots.into_iter().enumerate() {
            self.slots.remove(slot_index - i);
        }

        // add the newly created slot
        self.slots.push(new_slot);

        // done
        Ok(())
    }

    fn select(
        &self,
        index: TempIndex,
        cond: &SmtExpr<'smt>,
    ) -> Result<Vec<(SymRefType, SmtExpr<'smt>)>> {
        let ctxt = self.ctxt;

        let mut result = vec![];
        for slot in &self.slots {
            // if we are not writing back to the slot, ignore it
            // TODO: my guess is that all slot_index should be the same as index
            if !match slot.refv {
                SymRefType::Local { slot_index } | SymRefType::Field { slot_index, .. } => {
                    slot_index == index
                }
            } {
                continue;
            }

            // check feasibility
            let slot_cond = slot.cond.and(cond);
            if !ctxt.is_feasible_assume_solvable(&[&slot_cond])? {
                continue;
            }

            // add to return list
            result.push((slot.refv.clone(), slot_cond));
        }

        Ok(result)
    }

    fn select_all(&self, cond: &SmtExpr<'smt>) -> Result<Vec<(SymRefType, SmtExpr<'smt>)>> {
        let ctxt = self.ctxt;

        let mut result = vec![];
        for slot in &self.slots {
            // filter out infeasible options
            let slot_cond = slot.cond.and(cond);
            if !ctxt.is_feasible_assume_solvable(&[&slot_cond])? {
                continue;
            }

            // add to return list
            result.push((slot.refv.clone(), slot_cond));
        }

        Ok(result)
    }
}

/// A symbolic version maintaining the frame for an exec unit
pub(crate) struct SymFrame<'smt> {
    /// A symbolic version of the struct used in concrete execution
    locals: Vec<SymMemCell<'smt>>,
    /// A map of local indexes that are also references
    local_refs: BTreeMap<TempIndex, SymRefCell<'smt>>,
    /// Local indexes for receive values. Set when calls into another function
    /// and cleared when that function returns
    receive: Option<Vec<TempIndex>>,
    /// Local indexes for return values. Set when return from this function
    returns: Option<Vec<TempIndex>>,
}

impl<'smt> SymFrame<'smt> {
    pub fn new(ctxt: &'smt SmtCtxt, num_locals: usize, ref_indice: &[TempIndex]) -> Self {
        Self {
            locals: (0..num_locals).map(|_| SymMemCell::new(ctxt)).collect(),
            local_refs: ref_indice
                .iter()
                .map(|index| (*index, SymRefCell::new(ctxt)))
                .collect(),
            receive: None,
            returns: None,
        }
    }

    fn get_local_mut(&mut self, index: TempIndex) -> &mut SymMemCell<'smt> {
        self.locals.get_mut(index).unwrap()
    }

    fn get_local_ref(&self, index: TempIndex) -> &SymRefCell<'smt> {
        self.local_refs.get(&index).unwrap()
    }

    fn get_local_ref_mut(&mut self, index: TempIndex) -> &mut SymRefCell<'smt> {
        self.local_refs.get_mut(&index).unwrap()
    }

    pub fn store_local(
        &mut self,
        index: TempIndex,
        sym: &SymValue<'smt>,
        cond: &SmtExpr<'smt>,
    ) -> Result<()> {
        let cell = self.get_local_mut(index);
        cell.store(sym, cond)?;
        debug!("> [store {}]", index);
        debug!("> sym: {}", sym);
        debug!("> cell: {}", cell);
        debug!("> cond: {}", cond);
        Ok(())
    }

    pub fn move_local(&mut self, index: TempIndex, cond: &SmtExpr<'smt>) -> Result<SymValue<'smt>> {
        let cell = self.get_local_mut(index);
        let sym = cell.load(cond, true)?;
        debug!("> [move {}]", index);
        debug!("> sym: {}", sym);
        debug!("> cell: {}", cell);
        debug!("> cond: {}", cond);
        Ok(sym)
    }

    pub fn copy_local(&mut self, index: TempIndex, cond: &SmtExpr<'smt>) -> Result<SymValue<'smt>> {
        let cell = self.get_local_mut(index);
        let sym = cell.load(cond, false)?;
        debug!("> [copy {}]", index);
        debug!("> sym: {}", sym);
        debug!("> cell: {}", cell);
        debug!("> cond: {}", cond);
        Ok(sym)
    }

    pub fn destroy_local(&mut self, index: TempIndex, cond: &SmtExpr<'smt>) -> Result<()> {
        let cell = self.get_local_mut(index);
        cell.load(cond, true)?;
        debug!("> [destroy {}]", index);
        debug!("> cell: {}", cell);
        debug!("> cond: {}", cond);
        // TODO: check if any slots left
        Ok(())
    }

    pub fn is_local_ref(&self, index: TempIndex) -> bool {
        self.local_refs.contains_key(&index)
    }

    pub fn record_local_ref(
        &mut self,
        index: TempIndex,
        rty: &SymRefType,
        cond: &SmtExpr<'smt>,
    ) -> Result<()> {
        let cell = self.get_local_ref_mut(index);
        cell.record(rty, cond)?;
        debug!("> [record {}]", index);
        debug!("> rty: {}", rty);
        debug!("> cell: {}", cell);
        debug!("> cond: {}", cond);
        Ok(())
    }

    pub fn select_local_ref(
        &self,
        index: TempIndex,
        target: TempIndex,
        cond: &SmtExpr<'smt>,
    ) -> Result<Vec<(SymRefType, SmtExpr<'smt>)>> {
        let cell = self.get_local_ref(index);
        let res = cell.select(target, cond)?;
        debug!("> [select {}]", index);
        debug!(
            "> res: [\n{}\n]",
            res.iter()
                .map(|(ref_type, ref_cond)| format!("\t{}: {}", ref_type, ref_cond))
                .join("\n")
        );
        debug!("> cell: {}", cell);
        debug!("> cond: {}", cond);
        Ok(res)
    }

    pub fn transfer_local_ref(
        &mut self,
        src: TempIndex,
        dst: TempIndex,
        cond: &SmtExpr<'smt>,
    ) -> Result<()> {
        let src_slot = self.get_local_ref(src);
        let records = src_slot.select_all(cond)?;

        let dst_slot = self.get_local_ref_mut(dst);
        for (ref_type, ref_cond) in records.iter() {
            dst_slot.record(ref_type, ref_cond)?;
        }

        Ok(())
    }

    pub fn set_returns(&mut self, rets: &[TempIndex]) {
        // NOTE: check the assumption in stackless CFG that at max one return per function
        debug_assert!(self.returns.is_none());
        self.returns = Some(rets.to_vec());
    }

    pub fn has_returns(&self) -> bool {
        self.returns.is_some()
    }

    pub fn set_receive(&mut self, recs: &[TempIndex]) {
        // NOTE: check that last call (if any) has returned
        debug_assert!(self.receive.is_none());
        self.receive = Some(recs.to_vec())
    }

    pub fn receive_returns(&mut self, frame: &mut Self, cond: &SmtExpr<'smt>) -> Result<()> {
        let srcs = frame.returns.as_ref().unwrap().clone();
        let dsts = self.receive.as_ref().unwrap().clone();
        debug_assert_eq!(srcs.len(), dsts.len());
        for (src, dst) in srcs.into_iter().zip(dsts.into_iter()) {
            let sym = frame.copy_local(src, cond)?;
            self.store_local(dst, &sym, cond)?;
        }
        // clear the receive, mark that we are ready for the next call
        self.receive = None;
        Ok(())
    }
}

// utility
fn addr_to_uint(val: &AccountAddress) -> u128 {
    let (addr, _) = val
        .to_u8()
        .iter()
        .rev()
        .fold((0u128, 0u128), |(acc, mul), v| {
            (acc + ((*v as u128) << mul), mul + 8)
        });
    addr
}

// unit testing for vm types
#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn assumptions() {
        // check that we are using twice the number of bits for address
        assert_eq!(
            size_of::<AccountAddress>() * 8,
            ADDRESS_STRUCT_VALUE_FIELD_BITVEC_WIDTH as usize
        );
    }
}
