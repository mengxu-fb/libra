// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use bytecode::stackless_bytecode::{Bytecode, Operation};

use crate::{
    sym_exec_graph::{ExecGraph, ExecWalker, ExecWalkerStep},
    sym_oracle::SymOracle,
};

/// Records the dependencies between the types, especially structs, involved in the execution.
pub(crate) struct TypeGraph {}

impl TypeGraph {
    pub fn new<'env>(exec_graph: &ExecGraph<'env>, _oracle: &'env SymOracle<'env>) -> Self {
        // holds the block access path
        let mut scc_stack = vec![None];

        // find all places that may use a struct type
        let mut walker = ExecWalker::new(exec_graph);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::CycleEntry { scc_id } => scc_stack.push(Some(scc_id)),
                ExecWalkerStep::CycleExit { scc_id } => {
                    let cur_scc_id = scc_stack.pop().unwrap();
                    debug_assert_eq!(cur_scc_id.unwrap(), scc_id);
                }
                ExecWalkerStep::Block { block_id, .. } => {
                    // go ver the instructions
                    let block = exec_graph.get_block_by_block_id(block_id);
                    for instruction in &block.instructions {
                        if let Bytecode::Call(_, _, op, _) = instruction {}
                    }
                }
            }
        }

        // stack integrity
        let base_scc = scc_stack.pop().unwrap();
        debug_assert!(base_scc.is_none());
        debug_assert!(scc_stack.is_empty());

        // done
        TypeGraph {}
    }
}
