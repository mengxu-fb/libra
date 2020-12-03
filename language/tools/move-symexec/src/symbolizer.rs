// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use log::{debug, warn};
use serde_json::{self, json};
use std::{fs::File, io::Write, path::PathBuf};

use move_core_types::{account_address::AccountAddress, language_storage::TypeTag};
use vm::{
    access::ScriptAccess,
    file_format::{CompiledScript, SignatureToken},
};

use crate::{
    sym_exec_graph::{ExecGraph, ExecRefGraph, ExecSccGraph},
    sym_oracle::SymOracle,
    sym_type_graph::TypeGraph,
    sym_typing::ExecTypeArg,
    sym_vm::SymVM,
    sym_vm_types::SymTransactionArgument,
};

/// The default file name for the exec graph dot plot
const EXEC_GRAPH_DOT_FILE: &str = "exec_graph.dot";

/// The default file name for the exec graph statistics
const EXEC_GRAPH_STATS_FILE: &str = "exec_graph_stats.json";

/// The default file name for the type graph listing
const TYPE_GRAPH_LISTING_FILE: &str = "type_graph_listing.txt";

/// Limit of path count
const EXEC_GRAPH_PATH_ENUMERATION_LIMIT: u128 = std::u16::MAX as u128;

/// The symbolizer
pub(crate) struct MoveSymbolizer<'env> {
    workdir: PathBuf,
    script: &'env CompiledScript,
    oracle: &'env SymOracle<'env>,
    exec_graph: ExecGraph<'env>,
    type_graph: TypeGraph<'env>,
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

        // build exec graph
        let exec_graph = ExecGraph::new(&type_args, oracle);

        // build type graph
        let type_graph = TypeGraph::new(&exec_graph, oracle);

        // done
        Ok(Self {
            workdir,
            script,
            oracle,
            exec_graph,
            type_graph,
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

        // leave the rest to the VM
        let vm = SymVM::new(&self.oracle, &self.exec_graph, &self.type_graph);
        vm.interpret(if use_signers { Some(signers) } else { None }, sym_args);

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

        // build the ref graph
        let ref_graph = ExecRefGraph::from_graph(&self.exec_graph);

        // build the scc graph
        let scc_graph = ExecSccGraph::new(&ref_graph);

        // count paths with our handwritten algorithm
        let path_count = scc_graph.count_paths();
        debug!("{} paths in top-level scc graph", path_count);

        // cross-checking with the petgraph's algorithm
        if path_count > EXEC_GRAPH_PATH_ENUMERATION_LIMIT {
            warn!("path count exceeds limit, will not enumerate paths");
        } else {
            debug_assert_eq!(path_count, scc_graph.enumerate_paths().len() as u128);
        }

        // construct the stats json
        let stats = json!({
            "node_count": self.exec_graph.node_count(),
            "edge_count": self.exec_graph.edge_count(),
            "path_count": path_count.to_string(),  // u128 not supported
        });

        // save the stats to file
        let path = self.workdir.join(EXEC_GRAPH_STATS_FILE);
        serde_json::to_writer(&File::create(path)?, &stats)?;

        // done
        Ok(())
    }

    pub fn save_type_graph_listing(&self) -> Result<()> {
        // show number of types tracked
        debug!("{} types in type graph", self.type_graph.type_count());

        // write the sorted types to file
        let path = self.workdir.join(TYPE_GRAPH_LISTING_FILE);
        let mut fp = File::create(path)?;
        for (name, _) in self.type_graph.reverse_topological_sort() {
            writeln!(&mut fp, "{}", name)?;
        }

        // done
        Ok(())
    }
}
