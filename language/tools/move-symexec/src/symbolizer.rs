// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::path::PathBuf;

use move_core_types::{account_address::AccountAddress, language_storage::TypeTag};
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::sym_vm_types::SymTransactionArgument;

/// The symbolizer
#[derive(Clone, Debug)]
pub(crate) struct MoveSymbolizer {
    _workdir: PathBuf,
}

impl MoveSymbolizer {
    /// Create a new symbolizer, assuming that `workdir` is already created.
    pub fn new(workdir: PathBuf) -> Self {
        Self { _workdir: workdir }
    }

    pub fn symbolize(
        &mut self,
        script: &CompiledScript,
        signers: &[AccountAddress],
        sym_args: &[SymTransactionArgument],
        type_tags: &[TypeTag],
        _output_exec_graph: bool,
        _output_exec_graph_stats: bool,
    ) -> Result<()> {
        // check that we got the correct number of symbolic arguments
        let val_arg_sigs = script.signature_at(script.as_inner().parameters);
        let use_signers = !val_arg_sigs.is_empty()
            && match val_arg_sigs.0.get(0).unwrap() {
                SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                _ => false,
            };

        // NOTE: signers must come before value arguments, if present in the signature
        if val_arg_sigs.len() != if use_signers { signers.len() } else { 0 } + sym_args.len() {
            bail!("The number of symbols does not match the number of value arguments");
        }

        // check that we got the correct number of type arguments
        if type_tags.len() != script.as_inner().type_parameters.len() {
            bail!("The number of type tags does not match the number of type arguments");
        }

        // done
        Ok(())
    }
}
