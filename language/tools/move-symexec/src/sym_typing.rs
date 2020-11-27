// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use itertools::Itertools;
use std::fmt;

use move_core_types::{
    identifier::Identifier,
    language_storage::{ModuleId, TypeTag},
};
use vm::file_format::TypeParameterIndex;

// Flattened type tracking
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExecTypeArg {
    Bool,
    U8,
    U64,
    U128,
    Address,
    Signer,
    Vector {
        element_type: Box<ExecTypeArg>,
    },
    Struct {
        module_id: ModuleId,
        struct_name: Identifier,
        type_args: Vec<ExecTypeArg>,
    },
    Reference {
        referred_type: Box<ExecTypeArg>,
    },
    MutableReference {
        referred_type: Box<ExecTypeArg>,
    },
    TypeParameter {
        param_index: TypeParameterIndex,
        actual_type: Box<ExecTypeArg>,
    },
}

impl ExecTypeArg {
    pub fn convert_from_type_tag(tag: &TypeTag) -> ExecTypeArg {
        match tag {
            TypeTag::Bool => ExecTypeArg::Bool,
            TypeTag::U8 => ExecTypeArg::U8,
            TypeTag::U64 => ExecTypeArg::U64,
            TypeTag::U128 => ExecTypeArg::U128,
            TypeTag::Address => ExecTypeArg::Address,
            TypeTag::Signer => ExecTypeArg::Signer,
            TypeTag::Vector(element_tag) => ExecTypeArg::Vector {
                element_type: Box::new(ExecTypeArg::convert_from_type_tag(element_tag.as_ref())),
            },
            TypeTag::Struct(struct_tag) => ExecTypeArg::Struct {
                module_id: struct_tag.module_id(),
                struct_name: struct_tag.name.to_owned(),
                type_args: struct_tag
                    .type_params
                    .iter()
                    .map(ExecTypeArg::convert_from_type_tag)
                    .collect(),
            },
        }
    }
}

impl fmt::Display for ExecTypeArg {
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
                module_id,
                struct_name,
                type_args,
            } => write!(
                f,
                "struct {}::{}::{}<{}>",
                module_id.address().short_str_lossless(),
                module_id.name(),
                struct_name,
                type_args.iter().map(|ty_arg| ty_arg.to_string()).join(", ")
            ),
            ExecTypeArg::Reference { referred_type } => write!(f, "&{}", referred_type),
            ExecTypeArg::MutableReference { referred_type } => write!(f, "&mut {}", referred_type),
            ExecTypeArg::TypeParameter {
                param_index,
                actual_type,
            } => write!(f, "#{}-{}", param_index, actual_type),
        }
    }
}
