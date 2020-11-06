// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use log::warn;

use move_core_types::{account_address::AccountAddress, transaction_argument::TransactionArgument};
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::ExecGraph,
    sym_setup::{ExecStructInfo, ExecTypeArg},
    sym_smtlib::{SmtCtxt, SmtKind},
    sym_type_graph::TypeGraph,
    sym_vm_types::{SymLocals, SymTransactionArgument, SymValue},
};

/// Config: whether to simplify smt expressions upon construction
const CONF_SMT_AUTO_SIMPLIFY: bool = true;

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM<'a> {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// Maps all struct types to names of the corresponding smt types
    _type_graph: &'a TypeGraph,
}

impl<'a> SymVM<'a> {
    fn type_arg_to_smt_kind(type_arg: &ExecTypeArg, type_graph: &TypeGraph) -> SmtKind {
        match type_arg {
            ExecTypeArg::Bool => SmtKind::Bool,
            ExecTypeArg::U8 => SmtKind::bitvec_u8(),
            ExecTypeArg::U64 => SmtKind::bitvec_u64(),
            ExecTypeArg::U128 => SmtKind::bitvec_u128(),
            ExecTypeArg::Address => SmtKind::bitvec_address(),
            ExecTypeArg::Signer => SmtKind::bitvec_address(),
            ExecTypeArg::Vector { element_type } => SmtKind::Vector {
                element_kind: Box::new(SymVM::type_arg_to_smt_kind(
                    element_type.as_ref(),
                    type_graph,
                )),
            },
            ExecTypeArg::Struct { context, type_args } => SmtKind::Struct {
                struct_name: type_graph
                    .get_struct_name(context, type_args)
                    .unwrap()
                    .to_owned(),
            },
            ExecTypeArg::Reference { referred_type }
            | ExecTypeArg::MutableReference { referred_type } => SmtKind::Reference {
                referred_kind: Box::new(SymVM::type_arg_to_smt_kind(
                    referred_type.as_ref(),
                    type_graph,
                )),
            },
            ExecTypeArg::TypeParameter { actual_type, .. } => {
                SymVM::type_arg_to_smt_kind(actual_type.as_ref(), type_graph)
            }
        }
    }

    pub fn new(type_graph: &'a TypeGraph) -> Self {
        let mut smt_ctxt = SmtCtxt::new(CONF_SMT_AUTO_SIMPLIFY);

        // pre-compute the struct smt types
        for (struct_name, struct_info) in type_graph.reverse_topological_sort() {
            match struct_info {
                ExecStructInfo::Native => {
                    // TODO: we should have a dedicated modeling for
                    // native struct types
                    warn!("A native struct type is ignored: {}", struct_name)
                }
                ExecStructInfo::Declared {
                    field_vec,
                    field_map,
                } => {
                    let field_smt_kinds: Vec<(String, SmtKind)> = field_vec
                        .iter()
                        .map(|field_name| {
                            (
                                field_name.clone().into_string(),
                                SymVM::type_arg_to_smt_kind(
                                    field_map.get(field_name).unwrap(),
                                    type_graph,
                                ),
                            )
                        })
                        .collect();
                    smt_ctxt.create_smt_struct(struct_name.to_owned(), field_smt_kinds);
                }
            }
        }

        // done
        Self {
            smt_ctxt,
            _type_graph: type_graph,
        }
    }

    pub fn interpret(
        &self,
        script: &CompiledScript,
        type_args: &[ExecTypeArg],
        _exec_graph: &ExecGraph,
        signers: &[AccountAddress],
        sym_args: &[SymTransactionArgument],
    ) {
        // check that we got the correct number of type arguments
        debug_assert_eq!(type_args.len(), script.as_inner().type_parameters.len());

        // collect value signatures
        let val_arg_sigs = script.signature_at(script.as_inner().parameters);

        // check that we got the correct number of value arguments
        // NOTE: signers must come before value arguments, if present
        // in the signature
        let use_signers = !val_arg_sigs.is_empty()
            && match val_arg_sigs.0.get(0).unwrap() {
                SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                _ => false,
            };

        debug_assert_eq!(
            val_arg_sigs.len(),
            if use_signers { signers.len() } else { 0 } + sym_args.len()
        );

        // find value types other than signers
        let arg_index_start = if use_signers {
            let num_signers = signers.len();
            debug_assert_ne!(num_signers, 0);
            debug_assert!(
                (1..num_signers).all(|i| match val_arg_sigs.0.get(i).unwrap() {
                    SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                    _ => false,
                })
            );
            num_signers
        } else {
            0
        };

        // turn transaction argument into values
        let mut sym_inputs: Vec<SymValue> = vec![];
        if use_signers {
            for signer in signers {
                sym_inputs.push(SymValue::from_transaction_argument(
                    &self.smt_ctxt,
                    &SignatureToken::Signer,
                    &SymTransactionArgument::Concrete(TransactionArgument::Address(*signer)),
                ));
            }
        }
        for (i, arg) in sym_args.iter().enumerate() {
            sym_inputs.push(SymValue::from_transaction_argument(
                &self.smt_ctxt,
                val_arg_sigs.0.get(arg_index_start + i).unwrap(),
                arg,
            ));
        }

        // prepare the init locals: the locals consist of two parts
        // - the arguments, which have initial symbolic values set and
        // - the local variables, which are empty in the beginning
        let init_local_sigs = script.signature_at(script.code().locals);
        SymLocals::new(sym_inputs.len() + init_local_sigs.len(), &sym_inputs);
    }
}
