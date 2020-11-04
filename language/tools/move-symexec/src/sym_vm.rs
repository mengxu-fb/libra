// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use log::debug;
use std::collections::{HashMap, HashSet};

use move_core_types::account_address::AccountAddress;
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::ExecGraph,
    sym_setup::{ExecTypeArg, StructContext, StructInfo, SymSetup},
    sym_smtlib::SmtCtxt,
    sym_vm_types::{SymTransactionArgument, SymValue},
};

/// Config: whether to simplify smt expressions upon construction
const CONF_SMT_AUTO_SIMPLIFY: bool = true;

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// Maps all struct types to names of the corresponding smt types
    _smt_struct_names: HashMap<StructContext, HashMap<Vec<ExecTypeArg>, String>>,
}

impl SymVM {
    pub fn new(
        setup: &SymSetup,
        involved_structs: &HashMap<StructContext, HashSet<Vec<ExecTypeArg>>>,
    ) -> Self {
        let mut smt_struct_names = HashMap::new();

        // pre-construct the smt types for structs
        for (struct_context, struct_variants) in involved_structs {
            let struct_info = setup.get_struct_info_by_context(struct_context).unwrap();

            if let StructInfo::Declared { .. } = struct_info {
                for (i, struct_inst) in struct_variants.iter().enumerate() {
                    let smt_name = format!("{}-{}", struct_context, i);
                    let exists = smt_struct_names
                        .entry(struct_context.clone())
                        .or_insert_with(HashMap::new)
                        .insert(struct_inst.clone(), smt_name.clone());
                    debug_assert!(exists.is_none());
                }
            } else {
                debug!("Ignoring native struct: {}", struct_context);
            }
        }
        // done
        Self {
            smt_ctxt: SmtCtxt::new(CONF_SMT_AUTO_SIMPLIFY),
            _smt_struct_names: smt_struct_names,
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
        // collect value signatures
        let val_arg_sigs = script.signature_at(script.as_inner().parameters);
        let _init_local_sigs = script.signature_at(script.code().locals);

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
        let _sym_inputs: Vec<SymValue> = sym_args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                SymValue::from_transaction_argument(
                    &self.smt_ctxt,
                    val_arg_sigs.0.get(arg_index_start + i).unwrap(),
                    arg,
                )
            })
            .collect();

        // check that we got the correct number of type arguments
        debug_assert_eq!(type_args.len(), script.as_inner().type_parameters.len());
    }
}
