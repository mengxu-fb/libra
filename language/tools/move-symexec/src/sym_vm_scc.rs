// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use crate::{
    sym_exec_graph::{ExecGraph, ExecRefGraph, ExecScc, ExecWalker, ExecWalkerStep},
    sym_oracle::get_instruction_defs_and_uses,
};

pub(crate) struct SymSccAnalysis {}

impl SymSccAnalysis {
    /// Find the phi nodes in this scc representing a loop.
    ///
    /// In the loop scc case, a phi node is a variable that
    /// - is used without first defining it in a dominating position in the loop and
    /// - is subsequently re-defined in the loop after at least one use
    ///
    /// In other words, the variable x is NOT a phi node if
    /// - x is not even defined in the loop, or
    /// - x is not even used in the loop, or
    /// - x is defined at N places and all uses of x can be partitioned into N subsets such that
    ///   - Def location Di dominates all uses in set Ui and
    ///   - Def location Di is not reachable to all other uses in U except those in Ui
    ///
    /// If there is a function call inside this loop, the blocks in the called function is ignored
    fn find_phi_nodes_in_loop(exec_graph: &ExecGraph, scc: &ExecScc) {
        let scc_func_id = exec_graph
            .get_block_by_block_id(scc.entry_block_id)
            .exec_unit
            .func_id;

        // holds the block access path
        let mut scc_stack = vec![(scc.scc_id, ExecRefGraph::from_graph_scc(exec_graph, scc))];

        // holds where each local variable is defined and used
        let mut local_defs = BTreeMap::new();
        let mut local_uses = BTreeMap::new();

        let mut walker = ExecWalker::new_from_scc(exec_graph, scc);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::CycleEntry { scc, .. } => {
                    scc_stack.push((scc.scc_id, ExecRefGraph::from_graph_scc(exec_graph, &scc)))
                }
                ExecWalkerStep::CycleExit { scc_id } => {
                    let (cur_scc_id, _) = scc_stack.pop().unwrap();
                    debug_assert_eq!(cur_scc_id, scc_id);
                }
                ExecWalkerStep::Block { block_id, .. } => {
                    let block = exec_graph.get_block_by_block_id(block_id);
                    if block.exec_unit.func_id != scc_func_id {
                        // skip function calls, as its effect has been summarized
                        continue;
                    }

                    for (pos, instruction) in block.instructions.iter().enumerate() {
                        let (defs, uses) = get_instruction_defs_and_uses(instruction);
                        for i in defs {
                            local_defs
                                .entry(i)
                                .or_insert_with(BTreeMap::new)
                                .insert(block_id, pos);
                        }
                        for i in uses {
                            local_uses
                                .entry(i)
                                .or_insert_with(BTreeMap::new)
                                .insert(block_id, pos);
                        }
                    }
                }
            }
        }

        // stack integrity
        debug_assert!(scc_stack.is_empty());

        // TODO: hack
        let scc_func_target = exec_graph
            .get_block_by_block_id(scc.entry_block_id)
            .exec_unit
            .get_target();

        for (k, v) in local_defs {
            let local_name = scc_func_target
                .symbol_pool()
                .string(scc_func_target.get_local_name(k));
            for (block_id, offset) in v {
                println!("{}: <- Block {} :: offset {}", local_name, block_id, offset);
            }
        }

        for (k, v) in local_uses {
            let local_name = scc_func_target
                .symbol_pool()
                .string(scc_func_target.get_local_name(k));
            for (block_id, offset) in v {
                println!("{}: -> Block {} :: offset {}", local_name, block_id, offset);
            }
        }

        // now try to find the phi nodes

    }

    fn find_phi_nodes(exec_graph: &ExecGraph, scc: &ExecScc) {
        // TODO: handle the recursion case
        SymSccAnalysis::find_phi_nodes_in_loop(exec_graph, scc)
    }

    pub fn new(exec_graph: &ExecGraph, scc: &ExecScc) -> Self {
        SymSccAnalysis::find_phi_nodes(exec_graph, scc);
        Self {}
    }
}
