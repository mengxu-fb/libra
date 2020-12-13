// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use bytecode::stackless_bytecode::{Bytecode, TempIndex};

use crate::{
    sym_exec_graph::{
        ExecGraph, ExecRefGraph, ExecScc, ExecSccId, ExecSccType, ExecWalker, ExecWalkerStep,
    },
    sym_oracle::get_instruction_defs_and_uses,
};

pub(crate) struct SymSccAnalysis {
    pub scc_id: ExecSccId,
    _phi_nodes: BTreeSet<TempIndex>,
}

impl SymSccAnalysis {
    /// Find the phi nodes in this scc representing a loop.
    ///
    /// A variable x is a phi node if
    /// - x is defined at least once in the loop, and
    /// - x is used at least once in the loop, and
    /// - after dropping the back edge, there still exists at least one path from one of the uses
    ///   to one of the defs.
    ///
    /// If there is a function call inside this loop, the blocks in the called function is ignored
    fn find_phi_nodes_in_loop(exec_graph: &ExecGraph, scc: &ExecScc) -> BTreeSet<TempIndex> {
        let scc_func_id = exec_graph
            .get_block_by_block_id(scc.entry_block_id)
            .exec_unit
            .func_id;

        // holds the block access path
        let mut scc_stack = vec![scc.scc_id];

        // holds where each local variable is defined and used
        let mut local_defs = BTreeMap::new();
        let mut local_uses = BTreeMap::new();

        let mut walker = ExecWalker::new_from_scc(exec_graph, scc);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::CycleEntry { scc, .. } => scc_stack.push(scc.scc_id),
                ExecWalkerStep::CycleExit { scc_id } => {
                    debug_assert_eq!(scc_stack.pop().unwrap(), scc_id);
                }
                ExecWalkerStep::Block { block_id, .. } => {
                    let block = exec_graph.get_block_by_block_id(block_id);
                    if block.exec_unit.func_id != scc_func_id {
                        // skip function calls, as its effect has been summarized
                        continue;
                    }

                    let scc_depth = scc_stack.len();
                    for (pos, instruction) in block.instructions.iter().enumerate() {
                        let (defs, uses) = get_instruction_defs_and_uses(instruction);
                        for i in defs {
                            local_defs
                                .entry(i)
                                .or_insert_with(BTreeMap::new)
                                .entry(block_id)
                                .or_insert_with(BTreeMap::new)
                                .insert(pos, scc_depth);
                        }
                        for i in uses {
                            local_uses
                                .entry(i)
                                .or_insert_with(BTreeMap::new)
                                .entry(block_id)
                                .or_insert_with(BTreeMap::new)
                                .insert(pos, scc_depth);
                        }
                    }
                }
            }
        }

        // stack integrity
        debug_assert!(scc_stack.is_empty());

        // now try to find the phi nodes
        let scc_ref_graph = ExecRefGraph::from_graph_scc(exec_graph, scc);

        let mut phi_nodes = BTreeSet::new();
        for (local_index, def_locs) in local_defs.iter() {
            if let Some(use_locs) = local_uses.get(local_index) {
                for (use_loc_block_id, use_loc_pos_map) in use_locs {
                    for (use_loc_offset, use_loc_depth) in use_loc_pos_map {
                        for (def_loc_block_id, def_loc_pos_map) in def_locs {
                            for (def_loc_offset, def_loc_depth) in def_loc_pos_map {
                                if (*use_loc_depth != 1) && (*def_loc_depth != 1) {
                                    // this induction variable belongs to an inner cycle
                                    continue;
                                }

                                if use_loc_block_id == def_loc_block_id {
                                    if use_loc_offset <= def_loc_offset {
                                        phi_nodes.insert(*local_index);
                                    }
                                // NOTE: otherwise, with the condition that
                                // 1) there is no back edge, and
                                // 2) this block is on the target scc (given its depth is 1)
                                // we are sure that there is no way for the use to get to the def
                                } else if scc_ref_graph
                                    .is_reachable(*use_loc_block_id, *def_loc_block_id)
                                {
                                    phi_nodes.insert(*local_index);
                                }
                            }
                        }
                    }
                }
            }
        }

        // done
        phi_nodes
    }

    /// Find the phi nodes in this scc representing a call recursion
    ///
    /// A variable x is a phi node if and only if x is in the function argument list
    /// TODO: this is based on my gut feeling... I can't actually prove it...
    fn find_phi_nodes_in_rec_call(exec_graph: &ExecGraph, scc: &ExecScc) -> BTreeSet<TempIndex> {
        let call_entry_block = exec_graph.get_block_by_block_id(scc.entry_block_id);
        let params = call_entry_block.exec_unit.func_env.get_parameters();
        let target = call_entry_block.exec_unit.get_target();
        params
            .into_iter()
            .map(|param| *target.get_local_index(param.0).unwrap())
            .collect()
    }

    /// Find the phi nodes in this scc representing a return recursion
    ///
    /// A variable x is a phi node if and only if x is in the return values list
    /// TODO: this is based on my gut feeling... I can't actually prove it...
    fn find_phi_nodes_in_rec_ret(exec_graph: &ExecGraph, scc: &ExecScc) -> BTreeSet<TempIndex> {
        // NOTE: upon deciding that this scc is of return type, we already asserted that there is
        // only one exit block. So we can safely unwrap the first entry of exit_block_ids
        let call_return_block =
            exec_graph.get_block_by_block_id(*scc.exit_block_ids.iter().next().unwrap());
        match call_return_block.instructions.last().unwrap() {
            Bytecode::Ret(_, rets) => rets.iter().copied().collect(),
            _ => panic!("Invalid termination instruction for a return block in recursive scc"),
        }
    }

    fn find_phi_nodes(exec_graph: &ExecGraph, scc: &ExecScc) -> BTreeSet<TempIndex> {
        let scc_type = scc.get_type(exec_graph);
        match scc_type {
            ExecSccType::Loop => SymSccAnalysis::find_phi_nodes_in_loop(exec_graph, scc),
            ExecSccType::RecursiveCall => {
                SymSccAnalysis::find_phi_nodes_in_rec_call(exec_graph, scc)
            }
            ExecSccType::RecursiveRet(_) => {
                SymSccAnalysis::find_phi_nodes_in_rec_ret(exec_graph, scc)
            }
        }
    }

    pub fn new(exec_graph: &ExecGraph, scc: &ExecScc) -> Self {
        Self {
            scc_id: scc.scc_id,
            _phi_nodes: SymSccAnalysis::find_phi_nodes(exec_graph, scc),
        }
    }
}
