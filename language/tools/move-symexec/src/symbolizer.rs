// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::path::PathBuf;

use move_core_types::{account_address::AccountAddress, language_storage::TypeTag};
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::{sym_oracle::SymOracle, sym_typing::ExecTypeArg, sym_vm_types::SymTransactionArgument};

/// The symbolizer
pub(crate) struct MoveSymbolizer<'env> {
    _workdir: PathBuf,
    script: &'env CompiledScript,
    oracle: &'env SymOracle<'env>,
}

impl<'env> MoveSymbolizer<'env> {
    /// Create a new symbolizer, assuming that `workdir` is already created.
    pub fn new(
        workdir: PathBuf,
        script: &'env CompiledScript,
        oracle: &'env SymOracle<'env>,
        type_tags: &[TypeTag],
    ) -> Result<Self> {
        // check that we got the correct number of type arguments
        if type_tags.len() != script.as_inner().type_parameters.len() {
            bail!("The number of type tags does not match the number of type arguments");
        }

        // convert type args
        let type_args: Vec<ExecTypeArg> = type_tags
            .iter()
            .map(ExecTypeArg::convert_from_type_tag)
            .collect();

        // done
        Ok(Self {
            _workdir: workdir,
            script,
            oracle,
        })
    }

    pub fn symbolize(
        &self,
        signers: &[AccountAddress],
        sym_args: &[SymTransactionArgument],
    ) -> Result<()> {
        // check that we got the correct number of symbolic arguments
        let val_arg_sigs = self.script.signature_at(self.script.as_inner().parameters);
        let use_signers = !val_arg_sigs.is_empty()
            && match val_arg_sigs.0.get(0).unwrap() {
                SignatureToken::Reference(inner) => matches!(&**inner, SignatureToken::Signer),
                _ => false,
            };

        // NOTE: signers must come before value arguments, if present in the signature
        if val_arg_sigs.len() != if use_signers { signers.len() } else { 0 } + sym_args.len() {
            bail!("The number of symbols does not match the number of value arguments");
        }

        // done
        Ok(())
    }
}
