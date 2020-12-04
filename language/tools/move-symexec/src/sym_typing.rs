// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use itertools::Itertools;
use std::fmt;

use move_core_types::language_storage::TypeTag;
use spec_lang::ty::{PrimitiveType, Type};
use vm::file_format::TypeParameterIndex;

use crate::sym_oracle::{SymOracle, SymStructInfo};

/// Flattened type tracking
#[derive(Clone, Eq, PartialEq, Hash)]
pub(crate) enum ExecTypeArg<'env> {
    Bool,
    U8,
    U64,
    U128,
    Address,
    Signer,
    Vector {
        element_type: Box<ExecTypeArg<'env>>,
    },
    Struct {
        struct_info: &'env SymStructInfo<'env>,
        type_args: Vec<ExecTypeArg<'env>>,
    },
    Reference {
        mutable: bool,
        referred_type: Box<ExecTypeArg<'env>>,
    },
    TypeParameter {
        param_index: TypeParameterIndex,
        actual_type: Box<ExecTypeArg<'env>>,
    },
}

impl<'env> ExecTypeArg<'env> {
    pub fn convert_from_type_tag(
        tag: &TypeTag,
        oracle: &'env SymOracle<'env>,
    ) -> ExecTypeArg<'env> {
        match tag {
            TypeTag::Bool => ExecTypeArg::Bool,
            TypeTag::U8 => ExecTypeArg::U8,
            TypeTag::U64 => ExecTypeArg::U64,
            TypeTag::U128 => ExecTypeArg::U128,
            TypeTag::Address => ExecTypeArg::Address,
            TypeTag::Signer => ExecTypeArg::Signer,
            TypeTag::Vector(element_tag) => ExecTypeArg::Vector {
                element_type: Box::new(ExecTypeArg::convert_from_type_tag(
                    element_tag.as_ref(),
                    oracle,
                )),
            },
            TypeTag::Struct(struct_tag) => ExecTypeArg::Struct {
                struct_info: oracle
                    .get_defined_struct_by_move(&struct_tag.module_id(), &struct_tag.name)
                    .unwrap(),
                type_args: struct_tag
                    .type_params
                    .iter()
                    .map(|sub_tag| ExecTypeArg::convert_from_type_tag(sub_tag, oracle))
                    .collect(),
            },
        }
    }

    pub fn convert_from_type_actual(
        actual: &Type,
        type_args: &[ExecTypeArg<'env>],
        oracle: &'env SymOracle<'env>,
    ) -> ExecTypeArg<'env> {
        match actual {
            Type::Primitive(primitive_type) => match primitive_type {
                PrimitiveType::Bool => ExecTypeArg::Bool,
                PrimitiveType::U8 => ExecTypeArg::U8,
                PrimitiveType::U64 => ExecTypeArg::U64,
                PrimitiveType::U128 => ExecTypeArg::U128,
                PrimitiveType::Address => ExecTypeArg::Address,
                PrimitiveType::Signer => ExecTypeArg::Signer,
                // these types only appear in specifications
                PrimitiveType::Num | PrimitiveType::Range | PrimitiveType::TypeValue => {
                    panic!("Found specification types in programs")
                }
            },
            Type::Vector(element_type) => ExecTypeArg::Vector {
                element_type: Box::new(ExecTypeArg::convert_from_type_actual(
                    element_type.as_ref(),
                    type_args,
                    oracle,
                )),
            },
            Type::Struct(module_id, struct_id, sub_type_args) => ExecTypeArg::Struct {
                struct_info: oracle
                    .get_defined_struct_by_spec(&module_id, &struct_id)
                    .unwrap(),
                type_args: sub_type_args
                    .iter()
                    .map(|sub_type_arg| {
                        ExecTypeArg::convert_from_type_actual(sub_type_arg, type_args, oracle)
                    })
                    .collect(),
            },
            Type::Reference(mutable, referred_type) => ExecTypeArg::Reference {
                mutable: *mutable,
                referred_type: Box::new(ExecTypeArg::convert_from_type_actual(
                    referred_type.as_ref(),
                    type_args,
                    oracle,
                )),
            },
            Type::TypeParameter(index) => {
                let indexed_type = type_args.get(*index as usize).unwrap().clone();
                match &indexed_type {
                    ExecTypeArg::TypeParameter { .. } => indexed_type,
                    _ => ExecTypeArg::TypeParameter {
                        param_index: *index,
                        actual_type: Box::new(indexed_type),
                    },
                }
            }
            // these types only appear in specification
            Type::Tuple(..)
            | Type::Fun(..)
            | Type::TypeDomain(..)
            | Type::TypeLocal(..)
            | Type::Var(..)
            | Type::Error => panic!("Found specification types in programs"),
        }
    }
}

impl fmt::Display for ExecTypeArg<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExecTypeArg::Bool => write!(f, "bool"),
            ExecTypeArg::U8 => write!(f, "u8"),
            ExecTypeArg::U64 => write!(f, "u64"),
            ExecTypeArg::U128 => write!(f, "u128"),
            ExecTypeArg::Address => write!(f, "address"),
            ExecTypeArg::Signer => write!(f, "signer"),
            ExecTypeArg::Vector { element_type } => write!(f, "vector<{}>", element_type),
            ExecTypeArg::Struct {
                struct_info,
                type_args,
            } => write!(
                f,
                "struct {}<{}>",
                struct_info.get_context_string(),
                type_args.iter().map(|ty_arg| ty_arg.to_string()).join(", ")
            ),
            ExecTypeArg::Reference {
                mutable,
                referred_type,
            } => write!(
                f,
                "&{} {}",
                if *mutable { "mut" } else { "" },
                referred_type
            ),
            ExecTypeArg::TypeParameter {
                param_index,
                actual_type,
            } => write!(f, "#{}-{}", param_index, actual_type),
        }
    }
}
