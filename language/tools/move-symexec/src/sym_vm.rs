// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use move_core_types::{account_address::AccountAddress, language_storage::TypeTag};
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::{ExecGraph, ExecWalker},
    sym_smtlib::SmtCtxt,
    sym_vm_types::{SymTransactionArgument, SymValue},
};

/// Config: whether to simplify smt expressions upon construction
const CONF_SMT_AUTO_SIMPLIFY: bool = true;

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
}

impl SymVM {
    pub fn new() -> Self {
        Self {
            smt_ctxt: SmtCtxt::new(CONF_SMT_AUTO_SIMPLIFY),
        }
    }

    pub fn interpret(
        &self,
        script: &CompiledScript,
        exec_graph: &ExecGraph,
        signers: &[AccountAddress],
        sym_args: &[SymTransactionArgument],
        type_args: &[TypeTag],
    ) {
        // collect value signatures
        let val_arg_sigs = script.signature_at(script.as_inner().parameters);
        let init_local_sigs = script.signature_at(script.code().locals);

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

        // TODO: code for exploration
        for sig in init_local_sigs.0.iter() {
            println!("{:?}", sig);
        }

        // run the walker
        let mut walker = ExecWalker::new(exec_graph);
        while walker.next().is_some() {}
    }
}
