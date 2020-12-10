// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use crate::{
    sym_exec_graph::{ExecGraph, ExecRefGraph, ExecScc, ExecWalker, ExecWalkerStep},
    sym_oracle::get_instruction_defs_and_uses,
};

pub(crate) struct SymSccAnalysis {}

impl SymSccAnalysis {
    /// Locate the induction variables in this scc representing a loop.
    ///
    /// In the loop scc case, an induction variable is a variable that
    /// - is used without first defining it in a dominating position in the loop and
    /// - is subsequently re-defined in the loop after at least one use
    ///
    /// In other words, the variable x is NOT an indvar if
    /// - x is not even defined in the loop, or
    /// - x is not even used in the loop, or
    /// - x is defined at N places and all uses of x can be partitioned into N subsets such that
    ///   - Def location Di dominates all uses in set Ui and
    ///   - Def location Di is not reachable to all other uses in U except those in Ui
    fn find_indvars_in_loop(exec_graph: &ExecGraph, scc: &ExecScc) {
        // holds the block access path
        let mut scc_stack = vec![(scc.scc_id, ExecRefGraph::from_graph_scc(exec_graph, scc))];

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
        let (base_scc_id, _) = scc_stack.pop().unwrap();
        debug_assert_eq!(base_scc_id, scc.scc_id);
        debug_assert!(scc_stack.is_empty());

        // TODO: hack
        println!("{:?}", local_defs);
        println!("{:?}", local_uses);
    }

    fn find_indvars(exec_graph: &ExecGraph, scc: &ExecScc) {
        // TODO: handle the recursion case
        SymSccAnalysis::find_indvars_in_loop(exec_graph, scc)
    }

    pub fn new(exec_graph: &ExecGraph, scc: &ExecScc) -> Self {
        SymSccAnalysis::find_indvars(exec_graph, scc);
        Self {}
    }
}
