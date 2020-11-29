// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::debug;
use serde_json::{self, json};
use std::{fs::File, io::Write, path::PathBuf};

use move_core_types::{account_address::AccountAddress, language_storage::TypeTag};
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::ExecGraph, sym_oracle::SymOracle, sym_typing::ExecTypeArg,
    sym_vm_types::SymTransactionArgument,
};

/// The default file name for the exec graph dot plot
const EXEC_GRAPH_DOT_FILE: &str = "exec_graph.dot";

/// The default file name for the exec graph statistics
const EXEC_GRAPH_STATS_FILE: &str = "exec_graph_stats.json";

/// The symbolizer
pub(crate) struct MoveSymbolizer<'env> {
    workdir: PathBuf,
    script: &'env CompiledScript,
    oracle: &'env SymOracle<'env>,
    exec_graph: ExecGraph<'env>,
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
            .map(|tag| ExecTypeArg::convert_from_type_tag(tag, oracle))
            .collect();

        // build execution graph
        let exec_graph = ExecGraph::new(&type_args, oracle);

        // done
        Ok(Self {
            workdir,
            script,
            oracle,
            exec_graph,
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

    pub fn save_exec_graph(&self) -> Result<()> {
        let path = self.workdir.join(EXEC_GRAPH_DOT_FILE);
        let mut file = File::create(path)?;
        file.write_all(self.exec_graph.to_dot().as_bytes())?;
        Ok(())
    }

    pub fn save_exec_graph_stats(&self) -> Result<()> {
        // show node and edge stats
        debug!(
            "{} nodes + {} edges in exec graph",
            self.exec_graph.node_count(),
            self.exec_graph.edge_count()
        );

        // construct the stats json
        let stats = json!({
            "node_count": self.exec_graph.node_count(),
            "edge_count": self.exec_graph.edge_count(),
        });

        // save the stats to file
        let path = self.workdir.join(EXEC_GRAPH_STATS_FILE);
        serde_json::to_writer(&File::create(path)?, &stats)?;

        // done
        Ok(())
    }
}
