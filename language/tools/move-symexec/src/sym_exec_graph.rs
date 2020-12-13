// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! This package aims for building an extended control-flow graph (eCFG) that encloses both script
//! and module per-function CFGs, i.e., a super graph that has CFGs connected by the call graph.

use itertools::Itertools;
use log::debug;
use petgraph::{
    algo::{all_simple_paths, has_path_connecting, tarjan_scc, toposort},
    dot::Dot,
    graph::{EdgeIndex, Graph, NodeIndex},
    visit::{Bfs, DfsPostOrder, EdgeRef},
    EdgeDirection,
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    iter::FromIterator,
    vec,
};

use bytecode::{
    stackless_bytecode::{Bytecode, Operation},
    stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph},
};
use vm::file_format::CodeOffset;

use crate::{
    sym_oracle::{SymFuncInfo, SymOracle},
    sym_typing::ExecTypeArg,
};
use std::fmt::Debug;

/// An id that uniquely identifies a basic block in the eCFG (i.e., `ExecGraph`)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct ExecBlockId(usize);

impl fmt::Display for ExecBlockId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// This is the basic block (i.e., the node) in the eCFG
pub(crate) struct ExecBlock<'env> {
    /// A unique identifier for the exec block
    pub block_id: ExecBlockId,
    /// The context (module, function) where this block lives
    pub exec_unit: &'env SymFuncInfo<'env>,
    /// The starting offset of the instructions in code context
    ///
    /// NOTE: A None value means that this is an arbitrary block which will host no instructions,
    /// vice versa, all arbitrary blocks will have None as code_offset
    pub code_offset: Option<CodeOffset>,
    /// The type argument for the function in the code context
    pub type_args: Vec<ExecTypeArg<'env>>,
    /// The instructions within this basic block. It is OK to be empty.
    pub instructions: Vec<&'env Bytecode>,
}

impl<'env> ExecBlock<'env> {
    fn new(
        block_id: ExecBlockId,
        exec_unit: &'env SymFuncInfo<'env>,
        code_offset: Option<CodeOffset>,
        type_args: Vec<ExecTypeArg<'env>>,
    ) -> Self {
        Self {
            block_id,
            exec_unit,
            code_offset,
            type_args,
            instructions: vec![],
        }
    }

    fn add_instruction(&mut self, bytecode: &'env Bytecode) {
        self.instructions.push(bytecode);
    }
}

impl<'env> fmt::Display for ExecBlock<'env> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // block head
        writeln!(
            f,
            "[{} - {}<{}> - {}]",
            self.block_id.0,
            self.exec_unit.get_context_string(),
            self.type_args
                .iter()
                .map(|ty_arg| ty_arg.to_string())
                .join(", "),
            self.code_offset
                .map_or_else(|| String::from("X"), |offset| offset.to_string())
        )?;

        // block content
        for instruction in self.instructions.iter() {
            writeln!(f, "{}", instruction.display(&self.exec_unit.get_target()))?;
        }

        // done
        Ok(())
    }
}

/// Types of control-flow transitions
#[derive(Clone)]
pub(crate) enum ExecFlowType {
    /// Conditional or unconditional (if condition is None) branch
    Branch(Option<bool>),
    /// Function call
    Call,
    /// Function return
    Ret(ExecBlockId),
    /// Recursive call
    CallRecursive,
    /// Recursive return
    RetRecursive(ExecBlockId),
}

impl fmt::Display for ExecFlowType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExecFlowType::Branch(cond) => write!(
                f,
                "Branch({})",
                cond.map_or_else(|| String::from("None"), |v| v.to_string())
            ),
            ExecFlowType::Call => write!(f, "Call"),
            ExecFlowType::Ret(block_id) => write!(f, "Ret({})", block_id),
            ExecFlowType::CallRecursive => write!(f, "CallRecursive"),
            ExecFlowType::RetRecursive(block_id) => write!(f, "RetRecursive({})", block_id),
        }
    }
}

/// This is the control-flow transition (i.e., the edge) in the eCFG
struct ExecFlow {
    /// The basic block where this flow goes from
    _src_block_id: ExecBlockId,
    /// The basic block where this flow goes into
    _dst_block_id: ExecBlockId,
    /// The type of this flow
    flow_type: ExecFlowType,
}

impl ExecFlow {
    pub fn new(
        _src_block_id: ExecBlockId,
        _dst_block_id: ExecBlockId,
        flow_type: ExecFlowType,
    ) -> Self {
        Self {
            _src_block_id,
            _dst_block_id,
            flow_type,
        }
    }
}

impl fmt::Display for ExecFlow {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.flow_type.fmt(f)
    }
}

/// Used to track information stored on the call stack
struct CallSite<'env> {
    /// The context we are in right now
    exec_unit: &'env SymFuncInfo<'env>,
    /// Instantiation information (if any).
    /// NOTE: Calls to the same function with different instantiations are treated as if this is
    /// calling different functions. This is part of the effort of flattening the types
    type_args: Vec<ExecTypeArg<'env>>,
    /// The exec block id for the entry block in this context
    entry_block_id: ExecBlockId,
}

/// This is the super-CFG graph representation.
pub(crate) struct ExecGraph<'env> {
    /// The graph structure
    graph: Graph<ExecBlock<'env>, ExecFlow>,
    /// A map mapping block id to node index
    node_map: HashMap<ExecBlockId, NodeIndex>,
    /// A map mapping a pair of connecting blocks to edge index
    edge_map: HashMap<(ExecBlockId, ExecBlockId), EdgeIndex>,
    /// The block id of the graph entry block
    entry_block_id: ExecBlockId,
    /// A list of blocks that are unreachable from the entry block
    dead_block_ids: HashSet<ExecBlockId>,
}

impl<'env> ExecGraph<'env> {
    // graph construction
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
            entry_block_id: ExecBlockId(0),
            dead_block_ids: HashSet::new(),
        }
    }

    fn add_block(&mut self, block: ExecBlock<'env>) -> NodeIndex {
        let block_id = block.block_id;
        let node_index = self.graph.add_node(block);
        let exists = self.node_map.insert(block_id, node_index);
        debug_assert!(exists.is_none());
        node_index
    }

    fn add_flow(
        &mut self,
        src_block_id: ExecBlockId,
        dst_block_id: ExecBlockId,
        flow_type: ExecFlowType,
    ) -> EdgeIndex {
        let edge_index = self.graph.add_edge(
            self.get_node_by_block_id(src_block_id),
            self.get_node_by_block_id(dst_block_id),
            ExecFlow::new(src_block_id, dst_block_id, flow_type),
        );
        let exists = self
            .edge_map
            .insert((src_block_id, dst_block_id), edge_index);
        debug_assert!(exists.is_none());
        edge_index
    }

    // information getters
    fn get_node_by_block_id(&self, block_id: ExecBlockId) -> NodeIndex {
        *self.node_map.get(&block_id).unwrap()
    }

    fn get_block_by_node(&self, node: NodeIndex) -> &ExecBlock<'env> {
        self.graph.node_weight(node).unwrap()
    }

    pub fn get_block_by_block_id(&self, block_id: ExecBlockId) -> &ExecBlock<'env> {
        self.get_block_by_node(self.get_node_by_block_id(block_id))
    }

    pub fn get_entry_block(&self) -> &ExecBlock<'env> {
        self.get_block_by_block_id(self.entry_block_id)
    }

    pub fn get_flow_by_block_ids(
        &self,
        src_block_id: ExecBlockId,
        dst_block_id: ExecBlockId,
    ) -> ExecFlowType {
        let edge = self.edge_map.get(&(src_block_id, dst_block_id)).unwrap();
        self.graph.edge_weight(*edge).unwrap().flow_type.clone()
    }

    fn get_outgoing_edges_for_block(
        &self,
        block_id: ExecBlockId,
    ) -> HashMap<ExecBlockId, ExecFlowType> {
        let src_node = self.get_node_by_block_id(block_id);
        self.graph
            .edges_directed(src_node, EdgeDirection::Outgoing)
            .map(|edge| {
                (
                    self.get_block_by_node(edge.target()).block_id,
                    edge.weight().flow_type.clone(),
                )
            })
            .collect()
    }

    // core
    fn incorporate(
        &mut self,
        exec_unit: &'env SymFuncInfo<'env>,
        type_args: &[ExecTypeArg<'env>],
        call_from_block_id: Option<ExecBlockId>,
        call_stack: &mut Vec<CallSite<'env>>,
        exit_table: &mut HashMap<ExecBlockId, HashSet<ExecBlockId>>,
        id_counter: &mut ExecBlockId,
        recursions: &mut HashMap<(ExecBlockId, ExecBlockId), ExecBlockId>,
        oracle: &'env SymOracle<'env>,
    ) -> (ExecBlockId, HashSet<ExecBlockId>) {
        // prepare
        let instructions = exec_unit.get_instructions();
        let cfg = &exec_unit.func_cfg;

        // maps instruction offset within one context to exec block id
        let mut inst_map: HashMap<CodeOffset, ExecBlockId> = HashMap::new();

        // maps a call instruction to a tuple
        // (call_from_exec_block_id, return_into_exec_block_id, Set<return_from_exec_block_id>)
        let mut call_inst_map: HashMap<
            CodeOffset,
            (ExecBlockId, ExecBlockId, HashSet<ExecBlockId>),
        > = HashMap::new();

        // locate the entry block of this function CFG
        let mut entry_point = None;

        // iterate CFG with reverse postorder DFS
        for block_id in cfg_reverse_postorder_dfs(&cfg, instructions) {
            // prepare
            let block_code_offset_lower = cfg.block_start(block_id);
            let block_code_offset_upper = cfg.block_end(block_id);

            // create the block
            let mut exec_block = ExecBlock::new(
                *id_counter,
                exec_unit,
                Some(block_code_offset_lower),
                type_args.to_vec(),
            );
            id_counter.0 += 1;

            // prepare call stack if this is the entry block
            //
            // NOTE: cfg.entry_blocks() must return one and only one BlockId. We checked this when
            // the CFG is constructed in `SymFuncInfo::new()`
            //
            // NOTE: since we traverse the CFG in reverse postorder dfs, this is guaranteed to be
            // executed before any other blocks are visited
            if block_id == cfg.entry_blocks().pop().unwrap() {
                debug_assert!(entry_point.is_none());
                entry_point = Some(exec_block.block_id);

                let call_site = CallSite {
                    exec_unit,
                    type_args: type_args.to_vec(),
                    entry_block_id: exec_block.block_id,
                };
                call_stack.push(call_site);
            }

            // scan instructions
            for offset in block_code_offset_lower..=block_code_offset_upper {
                let instruction = &instructions[offset as usize];
                exec_block.add_instruction(instruction);

                // now update the local instruction map
                let exists = inst_map.insert(offset, exec_block.block_id);
                debug_assert!(exists.is_none());

                // ensure that all branch instructions are terminations in the block
                if instruction.is_branch() {
                    debug_assert_eq!(offset, block_code_offset_upper);
                }

                // see if we are going to call into another exec unit
                if let Bytecode::Call(
                    _,
                    _,
                    Operation::Function(module_id, func_id, type_actuals),
                    _,
                ) = instruction
                {
                    if let Some(next_exec_unit) =
                        oracle.get_tracked_function_by_spec(module_id, func_id)
                    {
                        let next_type_args: Vec<ExecTypeArg> = type_actuals
                            .iter()
                            .map(|type_actual| {
                                ExecTypeArg::convert_from_type_actual(
                                    type_actual,
                                    type_args,
                                    oracle,
                                )
                            })
                            .collect();

                        // record block id
                        let call_site_block_id = exec_block.block_id;

                        // done with building of this exec block
                        self.add_block(exec_block);

                        // NOTE: we know that the termination instruction of every basic block in a
                        // stackless CFG must be a branch instruction, hence, a call can never be
                        // the termination instruction, hence this inequality assertion.
                        debug_assert_ne!(offset, block_code_offset_upper);

                        // clear this exec block so that it can be reused to host the rest of
                        // instructions in current basic block, after the call.
                        exec_block = ExecBlock::new(
                            *id_counter,
                            exec_unit,
                            Some(offset + 1),
                            type_args.to_vec(),
                        );
                        id_counter.0 += 1;

                        // record the block id that the call will return to
                        let call_site_ret_block_id = exec_block.block_id;

                        // check recursion and act accordingly
                        let rec_candidates: Vec<&CallSite> = call_stack
                            .iter()
                            .filter(|call_site| {
                                call_site.exec_unit == next_exec_unit
                                    && call_site.type_args == next_type_args
                            })
                            .collect();

                        let ret_block_ids = if rec_candidates.is_empty() {
                            // non-recursive: call into the next unit
                            self.incorporate(
                                next_exec_unit,
                                &next_type_args,
                                Some(call_site_block_id),
                                call_stack,
                                exit_table,
                                id_counter,
                                recursions,
                                oracle,
                            )
                            .1
                        } else {
                            // recursive call: do not further expand the CFG of that function, just
                            // connect the blocks.

                            // ensure no duplicated context in call stack
                            debug_assert_eq!(rec_candidates.len(), 1);

                            // mark that there should be a pending call edge from this block to the
                            // beginning of the call site context, and also that the context will
                            // return to the ret block.
                            let rec_call_site = *rec_candidates.last().unwrap();
                            let exists = recursions.insert(
                                (call_site_block_id, rec_call_site.entry_block_id),
                                call_site_ret_block_id,
                            );
                            debug_assert!(exists.is_none());

                            // intentionally return an empty list as the recursive call site has not
                            // finished CFG exploration, and hence, we do not know all of their
                            // return blocks yet.
                            HashSet::new()
                        };

                        // add the new block id to the map that tracks calls specifically
                        let exists = call_inst_map.insert(
                            offset,
                            (call_site_block_id, call_site_ret_block_id, ret_block_ids),
                        );
                        debug_assert!(exists.is_none());
                    }
                }
            }

            // add block to graph
            self.add_block(exec_block);
        }

        // pop the call stack after cfg exploration
        let call_site = call_stack.pop().unwrap();

        // add incoming call edge
        if let Some(exec_block_id) = call_from_block_id {
            // this exec unit is called into, add the call edge
            self.add_flow(exec_block_id, call_site.entry_block_id, ExecFlowType::Call);
        }

        // add branching edges in CFG
        let label_offsets = Bytecode::label_offsets(instructions);
        for block_id in cfg.blocks() {
            let term_offset = cfg.block_end(block_id);
            let term_instruction = &instructions[term_offset as usize];

            // it seems that in stackless CFG, every termination instruction is a branch
            debug_assert!(term_instruction.is_branch());
            let origin_block_id = inst_map.get(&term_offset).unwrap();

            for successor_offset in
                Bytecode::get_successors(term_offset, instructions, &label_offsets)
            {
                // exit instructions have no successors
                debug_assert!(!term_instruction.is_exit());

                // check which type of branch it is
                let exec_flow_type = if term_instruction.is_unconditional_branch() {
                    ExecFlowType::Branch(None)
                } else if let Bytecode::Branch(_, then_label, else_label, _) = term_instruction {
                    if successor_offset == *label_offsets.get(then_label).unwrap() {
                        ExecFlowType::Branch(Some(true))
                    } else {
                        debug_assert!(successor_offset == *label_offsets.get(else_label).unwrap());
                        ExecFlowType::Branch(Some(false))
                    }
                } else {
                    panic!("Invalid branch type for a termination instruction");
                };

                // add edge to graph
                self.add_flow(
                    *origin_block_id,
                    *inst_map.get(&successor_offset).unwrap(),
                    exec_flow_type,
                );
            }
        }

        // add returning edges from internal calls
        for (call_from_id, ret_into_id, ret_from_ids) in call_inst_map.values() {
            for ret_from_id in ret_from_ids {
                self.add_flow(*ret_from_id, *ret_into_id, ExecFlowType::Ret(*call_from_id));
            }
        }

        // collect blocks that ends with Ret
        let exit_points: HashSet<ExecBlockId> = instructions
            .iter()
            .enumerate()
            .filter_map(|(offset, instruction)| match instruction {
                Bytecode::Ret(..) => Some(*inst_map.get(&(offset as CodeOffset)).unwrap()),
                _ => None,
            })
            .collect();
        exit_table.insert(call_site.entry_block_id, exit_points.clone());

        // done
        (entry_point.unwrap(), exit_points)
    }

    pub fn new(type_args: &[ExecTypeArg<'env>], oracle: &'env SymOracle<'env>) -> Self {
        // find the init_unit
        let init_unit = oracle.get_script_exec_unit();

        // start symbolization from the init_unit
        let mut call_stack = vec![];
        let mut exit_table = HashMap::new();
        let mut id_counter = ExecBlockId(0);
        let mut recursions = HashMap::new();

        let mut exec_graph = ExecGraph::empty();
        let init_entry_point = exec_graph
            .incorporate(
                &init_unit,
                type_args,
                None,
                &mut call_stack,
                &mut exit_table,
                &mut id_counter,
                &mut recursions,
                oracle,
            )
            .0;

        // at the end of the execution, we should have no calls in stack
        debug_assert!(call_stack.is_empty());

        // add all recursion edges, this can only be done when incorporation is complete
        for ((call_from_id, call_into_id), ret_into_id) in recursions.iter() {
            // add call edge to graph
            exec_graph.add_flow(*call_from_id, *call_into_id, ExecFlowType::CallRecursive);

            // add return edges to graph
            for ret_from_id in exit_table.get(&call_into_id).unwrap() {
                exec_graph.add_flow(
                    *ret_from_id,
                    *ret_into_id,
                    ExecFlowType::RetRecursive(*call_from_id),
                );
            }
        }

        // check all nodes and edges are mapped
        debug_assert_eq!(exec_graph.graph.node_count(), exec_graph.node_map.len());
        debug_assert_eq!(exec_graph.graph.edge_count(), exec_graph.edge_map.len());

        // check that each node has at least one incoming edge, except for the entry node
        let mut entry_node = None;
        let mut exit_nodes = vec![];
        let mut dead_nodes = vec![];
        for node in exec_graph.graph.node_indices() {
            let exec_block = exec_graph.get_block_by_node(node);
            if exec_graph
                .graph
                .first_edge(node, EdgeDirection::Incoming)
                .is_none()
            {
                // we have not created any arbitrary blocks so far, should never see a None here
                if exec_block.code_offset.unwrap() == 0 {
                    // this is the true entry node
                    debug_assert!(entry_node.is_none());
                    entry_node = Some(node);
                } else {
                    dead_nodes.push(node);
                }
            }
            if exec_graph
                .graph
                .first_edge(node, EdgeDirection::Outgoing)
                .is_none()
            {
                let term_instruction = exec_graph
                    .graph
                    .node_weight(node)
                    .unwrap()
                    .instructions
                    .last()
                    .unwrap();

                // check that only Ret or Abort can be the termination instruction of an exit block
                debug_assert!(term_instruction.is_exit());
                exit_nodes.push(node);
            }
        }

        // log on dead nodes
        if !dead_nodes.is_empty() {
            debug!(
                "Found {} dead exec block(s) [{}]: this is likely caused by calling into some \
                function that never returns (e.g., a function with aborts only or is essentially \
                an infinite loop)",
                dead_nodes.len(),
                dead_nodes
                    .into_iter()
                    .map(|node| exec_graph.get_block_by_node(node).block_id.0.to_string())
                    .join(", ")
            )
        }

        // construct the entry node to this eCFG if not exists
        //
        // NOTE: if an entry node does not exist, this eCFG is essentially an infinite loop. To
        // handle this case, we create a dummy header block (i.e., containing no instructions) and
        // link the header with the first block of the init unit.
        if entry_node.is_none() {
            let header_block = ExecBlock::new(id_counter, init_unit, None, type_args.to_vec());
            id_counter.0 += 1;

            let header_block_id = header_block.block_id;
            let header_block_node = exec_graph.add_block(header_block);
            exec_graph.add_flow(
                header_block_id,
                init_entry_point,
                ExecFlowType::Branch(None),
            );

            // now set the header block node as the entry node
            entry_node = Some(header_block_node);
        }

        // this statement checks that entry_note must exist
        let entry_node = entry_node.unwrap();

        // set the entry block id
        exec_graph.entry_block_id = exec_graph.get_block_by_node(entry_node).block_id;

        // find all dead blocks
        let mut reachable_nodes = HashSet::new();

        let mut bfs = Bfs::new(&exec_graph.graph, entry_node);
        while let Some(node) = bfs.next(&exec_graph.graph) {
            reachable_nodes.insert(node);
        }

        for (block_id, node) in exec_graph.node_map.iter() {
            if !reachable_nodes.contains(node) {
                exec_graph.dead_block_ids.insert(*block_id);
            }
        }

        // done
        exec_graph
    }

    /// count number of nodes in the execution graph, including unreachable nodes from entry_block
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// count number of edges in the execution graph, including unreachable edges from entry_block
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// convert the graph into Dot representation
    pub fn to_dot(&self) -> String {
        format!(
            "{}",
            Dot::with_attr_getters(&self.graph, &[], &|_, _| "".to_string(), &|_, _| {
                "shape=box".to_string()
            })
        )
    }
}

/// A shadow graph that may refer to the whole or part (i.e., an scc) of the `ExecGraph`
pub(crate) struct ExecRefGraph {
    /// The graph structure
    graph: Graph<ExecBlockId, (ExecBlockId, ExecBlockId)>,
    /// A map mapping block id to node index
    node_map: HashMap<ExecBlockId, NodeIndex>,
    /// A map mapping a pair of connecting blocks to edge index
    edge_map: HashMap<(ExecBlockId, ExecBlockId), EdgeIndex>,
    /// The block id of the graph entry block
    entry_block_id: ExecBlockId,
}

impl ExecRefGraph {
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
            entry_block_id: ExecBlockId(0),
        }
    }

    fn add_block(&mut self, block_id: ExecBlockId) -> NodeIndex {
        let node_index = self.graph.add_node(block_id);
        let exists = self.node_map.insert(block_id, node_index);
        debug_assert!(exists.is_none());
        node_index
    }

    fn get_node_by_block_id(&self, block_id: ExecBlockId) -> NodeIndex {
        *self.node_map.get(&block_id).unwrap()
    }

    fn get_block_id_by_node(&self, node: NodeIndex) -> ExecBlockId {
        *self.graph.node_weight(node).unwrap()
    }

    fn add_flow(&mut self, src_block_id: ExecBlockId, dst_block_id: ExecBlockId) -> EdgeIndex {
        let edge_index = self.graph.add_edge(
            self.get_node_by_block_id(src_block_id),
            self.get_node_by_block_id(dst_block_id),
            (src_block_id, dst_block_id),
        );
        let exists = self
            .edge_map
            .insert((src_block_id, dst_block_id), edge_index);
        debug_assert!(exists.is_none());
        edge_index
    }

    fn populate(
        &mut self,
        exec_graph: &ExecGraph,
        scope_block_ids: &HashSet<ExecBlockId>,
        entry_block_id: ExecBlockId,
        break_scc: bool, // break cycles connecting to entry node
    ) {
        // add nodes
        for block_id in exec_graph.node_map.keys() {
            // only add blocks that belong to the scc
            if !scope_block_ids.contains(block_id) {
                continue;
            }
            self.add_block(*block_id);
        }

        // add edges
        for (src_block_id, dst_block_id) in exec_graph.edge_map.keys() {
            // only add edges that connects within the scc
            if !scope_block_ids.contains(src_block_id) || !scope_block_ids.contains(dst_block_id) {
                continue;
            }
            // drop back edges to the entry block (this is important when constructing for an scc)
            if break_scc && *dst_block_id == entry_block_id {
                continue;
            }
            self.add_flow(*src_block_id, *dst_block_id);
        }

        // set entry block
        self.entry_block_id = entry_block_id;
    }

    pub fn is_reachable(&self, src: ExecBlockId, dst: ExecBlockId) -> bool {
        has_path_connecting(
            &self.graph,
            self.get_node_by_block_id(src),
            self.get_node_by_block_id(dst),
            None,
        )
    }

    pub fn from_graph(exec_graph: &ExecGraph) -> Self {
        let scope_block_ids = HashSet::from_iter(exec_graph.node_map.keys().copied())
            .difference(&exec_graph.dead_block_ids)
            .copied()
            .collect();
        let mut ref_graph = ExecRefGraph::empty();
        ref_graph.populate(
            exec_graph,
            &scope_block_ids,
            exec_graph.entry_block_id,
            false,
        );
        ref_graph
    }

    pub fn from_graph_scc(exec_graph: &ExecGraph, scc: &ExecScc) -> Self {
        let mut ref_graph = ExecRefGraph::empty();
        ref_graph.populate(exec_graph, &scc.scope_block_ids, scc.entry_block_id, true);
        ref_graph
    }
}

/// An id that uniquely identifies an scc in an `ExecRefGraph`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct ExecSccId(usize);

impl fmt::Display for ExecSccId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An scc is a self-contained set of blocks (can be either a single block or a loop) in the shadow
/// graph of the eCFG, (i.e., in the `ExecRefGraph`)
#[derive(Clone)]
pub(crate) struct ExecScc {
    /// A unique identifier for the scc
    pub scc_id: ExecSccId,
    /// A set of block ids defining the scope of this scc
    pub scope_block_ids: HashSet<ExecBlockId>,
    /// The entry block in this scc
    pub entry_block_id: ExecBlockId,
    /// The exit blocks in this scc
    pub exit_block_ids: HashSet<ExecBlockId>,
    /// Whether this scc is cyclic with backedges to the entry block
    pub back_edges_from: HashSet<ExecBlockId>,
}

/// Marks the type of this scc
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) enum ExecSccType {
    Loop,
    RecursiveCall,
    RecursiveRet(ExecBlockId),
}

impl ExecScc {
    pub fn get_type(&self, exec_graph: &ExecGraph) -> ExecSccType {
        let mut scc_type = None;

        let entry_block = exec_graph.get_block_by_block_id(self.entry_block_id);
        if let Bytecode::Ret(..) = entry_block.instructions.last().unwrap() {
            // this is a recursive return block
            for back_from_block_id in self.back_edges_from.iter() {
                let flow_type =
                    exec_graph.get_flow_by_block_ids(*back_from_block_id, self.entry_block_id);
                debug_assert!(matches!(flow_type, ExecFlowType::Branch(None)));
            }

            // get the type
            debug_assert_eq!(self.exit_block_ids.len(), 1);
            let scc_out_edges = exec_graph
                .get_outgoing_edges_for_block(*self.exit_block_ids.iter().next().unwrap());
            debug_assert_eq!(scc_out_edges.len(), 2);
            for (_, flow_type) in scc_out_edges {
                match flow_type {
                    ExecFlowType::RetRecursive(paired_call) => {
                        debug_assert!(scc_type.is_none());
                        scc_type = Some(ExecSccType::RecursiveRet(paired_call));
                    }
                    ExecFlowType::Ret(_) => {}
                    _ => panic!("Invalid flow type for back edges"),
                }
            }
        } else {
            for back_from_block_id in self.back_edges_from.iter() {
                let flow_type =
                    exec_graph.get_flow_by_block_ids(*back_from_block_id, self.entry_block_id);
                match flow_type {
                    ExecFlowType::Branch(None) => {
                        if let Some(existing) = scc_type.as_ref() {
                            debug_assert_eq!(*existing, ExecSccType::Loop);
                        } else {
                            scc_type = Some(ExecSccType::Loop);
                        }
                    }
                    ExecFlowType::CallRecursive => {
                        if let Some(existing) = scc_type.as_ref() {
                            debug_assert_eq!(*existing, ExecSccType::RecursiveCall);
                        } else {
                            scc_type = Some(ExecSccType::RecursiveCall)
                        }
                    }
                    _ => panic!("Invalid flow type for back edges"),
                }
            }
        }

        scc_type.unwrap()
    }
}

/// A graph that condenses a `ExecRefGraph` into a scc graph
pub(crate) struct ExecSccGraph {
    /// The graph structure
    graph: Graph<ExecScc, (ExecBlockId, ExecBlockId)>,
    /// A map mapping scc id to node index
    node_map: HashMap<ExecSccId, NodeIndex>,
    /// A map mapping a pair of connecting sccs to a set of edge indices
    edge_map: HashMap<(ExecSccId, ExecSccId), HashSet<EdgeIndex>>,
    /// The scc that is marked as the entry of this scc graph
    entry_scc_id: ExecSccId,
    /// A set of sccs that have no outgoing edges
    exit_scc_ids: HashSet<ExecSccId>,
    /// Node-level linkage between exec graph to this scc graph
    linkage_node: HashMap<ExecBlockId, HashSet<ExecSccId>>,
    /// Edge-level linkage between exec graph to this scc graph
    linkage_edge: HashMap<(ExecBlockId, ExecBlockId), HashSet<(ExecSccId, ExecSccId)>>,
}

impl ExecSccGraph {
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
            entry_scc_id: ExecSccId(0),
            exit_scc_ids: HashSet::new(),
            linkage_node: HashMap::new(),
            linkage_edge: HashMap::new(),
        }
    }

    fn add_scc(&mut self, scc: ExecScc) -> NodeIndex {
        let scc_id = scc.scc_id;

        // establish linkage
        for block_id in scc.scope_block_ids.iter() {
            let non_exists = self
                .linkage_node
                .entry(*block_id)
                .or_insert_with(HashSet::new)
                .insert(scc_id);
            debug_assert!(non_exists);
        }

        // add node to graph
        let node_index = self.graph.add_node(scc);
        let exists = self.node_map.insert(scc_id, node_index);
        debug_assert!(exists.is_none());
        node_index
    }

    fn get_node_by_scc_id(&self, scc_id: ExecSccId) -> NodeIndex {
        *self.node_map.get(&scc_id).unwrap()
    }

    fn get_scc_by_node(&self, node: NodeIndex) -> &ExecScc {
        self.graph.node_weight(node).unwrap()
    }

    fn get_scc_by_scc_id(&self, scc_id: ExecSccId) -> &ExecScc {
        self.get_scc_by_node(self.get_node_by_scc_id(scc_id))
    }

    fn add_flow(
        &mut self,
        src_scc_id: ExecSccId,
        dst_scc_id: ExecSccId,
        src_block_id: ExecBlockId,
        dst_block_id: ExecBlockId,
    ) -> EdgeIndex {
        // establish linkage
        let non_exists = self
            .linkage_edge
            .entry((src_block_id, dst_block_id))
            .or_insert_with(HashSet::new)
            .insert((src_scc_id, dst_scc_id));
        debug_assert!(non_exists);

        // add edge to graph
        let edge_index = self.graph.add_edge(
            self.get_node_by_scc_id(src_scc_id),
            self.get_node_by_scc_id(dst_scc_id),
            (src_block_id, dst_block_id),
        );
        self.edge_map
            .entry((src_scc_id, dst_scc_id))
            .or_insert_with(HashSet::new)
            .insert(edge_index);
        edge_index
    }

    /// build the scc graph out of the exec shadow graph (i.e., the `ExecRefGraph`)
    pub fn new(ref_graph: &ExecRefGraph) -> Self {
        let mut scc_count = 0;
        let mut scc_graph = ExecSccGraph::empty();

        // holds the associated scc id that an edge is branching into
        //
        // NOTE: if a scc with multiple entries, the scc will be multiplexed, and each entering edge
        // is associated with one of the duplicated sccs
        let mut scc_edge_association: HashMap<(ExecBlockId, ExecBlockId), ExecSccId> =
            HashMap::new();

        // build the nodes and edges in the scc graph
        //
        // NOTE: this for-loop relies on a property of tarjan_scc
        //  - it iterates the sccs in reverse topological order
        for scc_nodes in tarjan_scc(&ref_graph.graph).into_iter() {
            // build the scope
            let scope_block_ids = HashSet::from_iter(
                scc_nodes
                    .iter()
                    .map(|node| ref_graph.get_block_id_by_node(*node)),
            );

            // find the entry blocks in this scc
            let mut scc_entry_map: HashMap<ExecBlockId, HashSet<ExecBlockId>> = HashMap::new();
            let mut scc_intra_edge_dst_block_ids = HashMap::new();
            for node in scc_nodes.iter() {
                for edge in ref_graph
                    .graph
                    .edges_directed(*node, EdgeDirection::Incoming)
                {
                    let (src_block_id, dst_block_id) = edge.weight();
                    // ignore edges within this scc, just mark the dst block id so we can tell
                    // whether this scc is cyclic with a back edge to the entry block
                    if scope_block_ids.contains(src_block_id) {
                        let non_exists = scc_intra_edge_dst_block_ids
                            .entry(*dst_block_id)
                            .or_insert_with(HashSet::new)
                            .insert(*src_block_id);
                        debug_assert!(non_exists);
                        continue;
                    }
                    // found an incoming edge into this scc
                    let non_exists = scc_entry_map
                        .entry(*dst_block_id)
                        .or_insert_with(HashSet::new)
                        .insert(*src_block_id);
                    debug_assert!(non_exists);
                }
            }

            // the only way when scc_entry_map is empty is that this scc contains the entry block
            // in the ref_graph, and vice versa
            if scc_entry_map.is_empty() {
                debug_assert!(scope_block_ids.contains(&ref_graph.entry_block_id));
                scc_entry_map.insert(ref_graph.entry_block_id, HashSet::new());
            }

            // collect edges branching out of this scc
            let mut outlet_map: HashMap<(ExecBlockId, ExecBlockId), ExecSccId> = HashMap::new();
            for node in scc_nodes.iter() {
                for edge in ref_graph
                    .graph
                    .edges_directed(*node, EdgeDirection::Outgoing)
                {
                    let (src_block_id, dst_block_id) = edge.weight();
                    // ignore edges within this scc
                    if scope_block_ids.contains(dst_block_id) {
                        continue;
                    }
                    // found an outgoing edge from this scc
                    let dst_scc_id = *scc_edge_association
                        .get(&(*src_block_id, *dst_block_id))
                        .unwrap();
                    let exists = outlet_map.insert((*src_block_id, *dst_block_id), dst_scc_id);
                    debug_assert!(exists.is_none());
                }
            }

            // register scc to scc graph
            for (scc_entry_block_id, foreign_block_ids) in scc_entry_map.into_iter() {
                let scc_id = ExecSccId(scc_count);
                scc_count += 1;

                // register this scc to graph
                scc_graph.add_scc(ExecScc {
                    scc_id,
                    scope_block_ids: scope_block_ids.clone(),
                    entry_block_id: scc_entry_block_id,
                    exit_block_ids: outlet_map
                        .iter()
                        .map(|((src_block_id, _), _)| *src_block_id)
                        .collect(),
                    back_edges_from: scc_intra_edge_dst_block_ids
                        .remove(&scc_entry_block_id)
                        .unwrap_or_else(HashSet::new),
                });

                // mark that all edges joining into this entry block are associated with this scc id
                for foreign_block_id in foreign_block_ids {
                    let exists =
                        scc_edge_association.insert((foreign_block_id, scc_entry_block_id), scc_id);
                    debug_assert!(exists.is_none());
                }

                // detect leaf scc
                if outlet_map.is_empty() {
                    let non_exists = scc_graph.exit_scc_ids.insert(scc_id);
                    debug_assert!(non_exists);
                }

                // add edges between sccs
                for ((src_block_id, dst_block_id), dst_scc_id) in outlet_map.iter() {
                    scc_graph.add_flow(scc_id, *dst_scc_id, *src_block_id, *dst_block_id);
                }
            }
        }

        // find the entry scc - as asserted before, the entry block in ref_graph can only be mapped
        // to one scc in the scc_graph
        let entry_scc_ids = scc_graph
            .linkage_node
            .get(&ref_graph.entry_block_id)
            .unwrap();
        debug_assert_eq!(entry_scc_ids.len(), 1);
        scc_graph.entry_scc_id = *entry_scc_ids.iter().next().unwrap();

        // done
        scc_graph
    }

    /// count paths
    pub fn count_paths(&self) -> u128 {
        // each path_end_scc (i.e., a leaf node in the scc graph) stores how many reachable paths
        // from any_scc to path_end_scc
        let mut path_map: HashMap<NodeIndex, HashMap<NodeIndex, u128>> = HashMap::new();

        // go with reverse topological order
        for node in toposort(&self.graph, None).unwrap().into_iter().rev() {
            let mut out_edges_iter = self
                .graph
                .edges_directed(node, EdgeDirection::Outgoing)
                .peekable();
            if out_edges_iter.peek().is_none() {
                // this is a termination scc
                let mut term_path_map = HashMap::new();
                term_path_map.insert(node, 1);
                let exists = path_map.insert(node, term_path_map);
                debug_assert!(exists.is_none());
            } else {
                // update path count map
                let mut scc_reach_map: HashMap<NodeIndex, u128> = HashMap::new();
                for out_edge in out_edges_iter {
                    for (path_end_scc, path_end_reach_map) in path_map.iter() {
                        if let Some(path_count) = path_end_reach_map.get(&out_edge.target()) {
                            // there is a way from this exit_scc to path_end_scc, add to count
                            let existing_count = scc_reach_map.entry(*path_end_scc).or_insert(0);
                            *existing_count += path_count;
                        }
                    }
                }

                // merge into the path map
                for (path_end_scc, path_end_reach_count) in scc_reach_map {
                    let exists = path_map
                        .get_mut(&path_end_scc)
                        .unwrap()
                        .insert(node, path_end_reach_count);
                    debug_assert!(exists.is_none());
                }
            }
        }

        // derive end-to-end path count
        let entry_scc_node = self.get_node_by_scc_id(self.entry_scc_id);
        let mut total_count = 0;
        for path_end_reach_map in path_map.values() {
            total_count += path_end_reach_map.get(&entry_scc_node).unwrap();
        }
        total_count
    }

    /// enumerate all paths from entry to the end
    pub fn enumerate_paths(&self) -> Vec<Vec<NodeIndex>> {
        let entry_scc_node = self.get_node_by_scc_id(self.entry_scc_id);
        let mut paths = vec![];
        for exit_scc_id in self.exit_scc_ids.iter() {
            if *exit_scc_id == self.entry_scc_id {
                // the all_simple_paths does not count single node path, hence we add it here to
                // reconcile with the output from the algorithm in scc_path_count
                paths.push(vec![]);
            } else {
                paths.extend(all_simple_paths::<Vec<NodeIndex>, _>(
                    &self.graph,
                    entry_scc_node,
                    self.get_node_by_scc_id(*exit_scc_id),
                    0,
                    None,
                ));
            }
        }
        paths
    }

    /// get all incoming edges into an scc, within this graph only
    pub fn get_incoming_edges_for_block(
        &self,
        scc_id: ExecSccId,
        block_id: ExecBlockId,
    ) -> Vec<(ExecSccId, ExecBlockId)> {
        // sanity checking
        let scc = self.get_scc_by_scc_id(scc_id);
        debug_assert!(scc.scope_block_ids.contains(&block_id));

        // collect incoming edges
        let dst_node = self.get_node_by_scc_id(scc_id);
        self.graph
            .edges_directed(dst_node, EdgeDirection::Incoming)
            .filter_map(|edge| {
                let (src_block_id, dst_block_id) = edge.weight();
                if *dst_block_id == block_id {
                    let src_node = edge.source();
                    Some((self.get_scc_by_node(src_node).scc_id, *src_block_id))
                } else {
                    None
                }
            })
            .collect()
    }

    /// get all outgoing edges from an scc, within this graph only
    pub fn get_outgoing_edges_for_block(
        &self,
        scc_id: ExecSccId,
        block_id: ExecBlockId,
    ) -> Vec<(ExecSccId, ExecBlockId)> {
        // sanity checking
        let scc = self.get_scc_by_scc_id(scc_id);
        debug_assert!(scc.scope_block_ids.contains(&block_id));

        // collect outgoing edges
        let src_node = self.get_node_by_scc_id(scc_id);
        self.graph
            .edges_directed(src_node, EdgeDirection::Outgoing)
            .filter_map(|edge| {
                let (src_block_id, dst_block_id) = edge.weight();
                if *src_block_id == block_id {
                    let dst_node = edge.target();
                    Some((self.get_scc_by_node(dst_node).scc_id, *dst_block_id))
                } else {
                    None
                }
            })
            .collect()
    }
}

/// Stores the internal states of the `ExecWalker`
struct ExecWalkerState {
    /// The scc we are currently exploring, w.r.t. the parent scc.
    /// If the scc is None, the walker is in the initial exec_graph. In other words, this scc can
    /// only be either the root exec graph as a whole or a cycle, or a cycle in a cycle, etc
    scc: Option<ExecScc>,
    /// The (sub) scc graph for this scc.
    sub_scc_graph: ExecSccGraph,
    /// A topological iterator for the (sub) scc_graph
    node_iterator: vec::IntoIter<NodeIndex>,
}

impl ExecWalkerState {
    fn from_base(exec_graph: &ExecGraph) -> Self {
        let ref_graph = ExecRefGraph::from_graph(exec_graph);
        let sub_scc_graph = ExecSccGraph::new(&ref_graph);
        let node_iterator = toposort(&sub_scc_graph.graph, None).unwrap().into_iter();
        Self {
            scc: None,
            sub_scc_graph,
            node_iterator,
        }
    }

    fn from_scc(exec_graph: &ExecGraph, scc: &ExecScc) -> Self {
        let ref_graph = ExecRefGraph::from_graph_scc(exec_graph, scc);
        let sub_scc_graph = ExecSccGraph::new(&ref_graph);
        let node_iterator = toposort(&sub_scc_graph.graph, None).unwrap().into_iter();
        Self {
            scc: Some(scc.clone()),
            sub_scc_graph,
            node_iterator,
        }
    }

    pub fn next(&mut self) -> Option<&ExecScc> {
        self.node_iterator
            .next()
            .map(move |node| self.sub_scc_graph.get_scc_by_node(node))
    }
}

enum CycleOrBlock {
    Cycle(ExecWalkerState),
    Block(ExecSccId, ExecBlockId),
}

pub(crate) enum ExecWalkerStep {
    /// Entering a new scc
    CycleEntry {
        /// The scc that we are about to descend to
        scc: ExecScc,
        /// Incoming edges into this scc (which is also to the scc entry block)
        incoming_edges: Vec<(ExecSccId, ExecBlockId)>,
    },
    /// Exiting the current scc, we have explored all blocks in it
    CycleExit { scc_id: ExecSccId },
    /// Moving into the next block within the current scc
    Block {
        /// The id of the scc that has this block (this scc has only this block, in fact)
        scc_id: ExecSccId,
        /// The block id
        block_id: ExecBlockId,
        /// Incoming edges into this block, within the enclosing scc
        incoming_edges: Vec<(ExecSccId, ExecBlockId)>,
        /// Outgoing edges from this block, within the enclosing scc
        outgoing_edges: Vec<(ExecSccId, ExecBlockId)>,
        /// Marks whether this block has back edges to the entry of any of its enclosing sccs
        scc_back_edges: HashMap<(ExecSccId, ExecBlockId), (usize, ExecSccId)>,
        /// Tracks which scc the edge exits (may or may not be the current exploring scc)
        scc_exit_edges: HashMap<(ExecSccId, ExecBlockId), (usize, ExecSccId)>,
    },
}

/// An iterator that visits each scc in the graph in a topological order
/// If this scc has a cycle, descend into this scc and iterate the scc
pub(crate) struct ExecWalker<'cfg, 'env> {
    exec_graph: &'cfg ExecGraph<'env>,
    iter_stack: Vec<ExecWalkerState>,
}

impl<'cfg, 'env> ExecWalker<'cfg, 'env> {
    pub fn new_from_base(exec_graph: &'cfg ExecGraph<'env>) -> Self {
        Self {
            exec_graph,
            iter_stack: vec![ExecWalkerState::from_base(exec_graph)],
        }
    }

    pub fn new_from_scc(exec_graph: &'cfg ExecGraph<'env>, scc: &ExecScc) -> Self {
        Self {
            exec_graph,
            iter_stack: vec![ExecWalkerState::from_scc(exec_graph, scc)],
        }
    }

    pub fn next(&mut self) -> Option<ExecWalkerStep> {
        // if we have nothing in the stack, we are done with the walking
        if self.iter_stack.is_empty() {
            return None;
        }

        // otherwise, we may need to update the stack before returning the next block
        let exec_graph = self.exec_graph;
        let state = self.iter_stack.last_mut().unwrap();
        let next_op = state.next().map(|scc| {
            if scc.back_edges_from.is_empty() {
                CycleOrBlock::Block(scc.scc_id, scc.entry_block_id)
            } else {
                CycleOrBlock::Cycle(ExecWalkerState::from_scc(exec_graph, scc))
            }
        });

        match next_op {
            None => {
                // internal scc yields nothing, pop the stack
                match self.iter_stack.pop().unwrap().scc {
                    None => self.next(), // NOTE: essentially returns None
                    Some(exiting_scc) => Some(ExecWalkerStep::CycleExit {
                        scc_id: exiting_scc.scc_id,
                    }),
                }
            }
            Some(cycle_or_block) => match cycle_or_block {
                CycleOrBlock::Cycle(state) => {
                    // we are about to descend into a new scc
                    let next_scc = state.scc.clone().unwrap();

                    // must happen before pushing the new state to iter_stack
                    let incoming_edges = self
                        .iter_stack
                        .last()
                        .unwrap()
                        .sub_scc_graph
                        .get_incoming_edges_for_block(next_scc.scc_id, next_scc.entry_block_id);

                    self.iter_stack.push(state);
                    Some(ExecWalkerStep::CycleEntry {
                        scc: next_scc,
                        incoming_edges,
                    })
                }
                CycleOrBlock::Block(scc_id, block_id) => {
                    // we continue to explore within the same scc
                    let incoming_edges = state
                        .sub_scc_graph
                        .get_incoming_edges_for_block(scc_id, block_id);

                    let outgoing_edges = state
                        .sub_scc_graph
                        .get_outgoing_edges_for_block(scc_id, block_id);

                    let mut scc_back_edges = HashMap::new();
                    let mut scc_exit_edges = HashMap::new();
                    if let Some(state_scc) = state.scc.as_ref() {
                        if state_scc.back_edges_from.contains(&block_id) {
                            let exists = scc_back_edges.insert(
                                (state.sub_scc_graph.entry_scc_id, state_scc.entry_block_id),
                                (0, state_scc.scc_id),
                            );
                            debug_assert!(exists.is_none());
                        }

                        let mut cursor_scc_id = state_scc.scc_id;
                        for (i, parent_state) in self.iter_stack.iter().rev().skip(1).enumerate() {
                            for pair in parent_state
                                .sub_scc_graph
                                .get_outgoing_edges_for_block(cursor_scc_id, block_id)
                            {
                                let exists = scc_exit_edges.insert(pair, (i, cursor_scc_id));
                                debug_assert!(exists.is_none());
                            }

                            if let Some(parent_state_scc) = parent_state.scc.as_ref() {
                                if parent_state_scc.back_edges_from.contains(&block_id) {
                                    let exists = scc_back_edges.insert(
                                        (
                                            parent_state.sub_scc_graph.entry_scc_id,
                                            parent_state_scc.entry_block_id,
                                        ),
                                        (i + 1, parent_state_scc.scc_id),
                                    );
                                    debug_assert!(exists.is_none());
                                }

                                // move the cursor to the parent level
                                cursor_scc_id = parent_state_scc.scc_id;
                            }
                        }
                    }

                    Some(ExecWalkerStep::Block {
                        scc_id,
                        block_id,
                        incoming_edges,
                        outgoing_edges,
                        scc_back_edges,
                        scc_exit_edges,
                    })
                }
            },
        }
    }
}

/// Convert a CFG into generic graphs so we can benefit from various graph algorithms in `petgraph`,
/// e.g., the `DfsPostOrder` visit algorithm
fn cfg_to_generic_graph(
    cfg: &StacklessControlFlowGraph,
    instructions: &[Bytecode],
) -> (Graph<BlockId, ()>, NodeIndex) {
    // convert a CFG into a generic graph provided by petgraph
    let mut graph = Graph::new();
    let blocks = cfg.blocks();

    // add nodes
    let node_map: HashMap<BlockId, NodeIndex> = blocks
        .iter()
        .map(|block_id| (*block_id, graph.add_node(*block_id)))
        .collect();

    // add edges
    blocks.iter().for_each(|block_id| {
        cfg.successors(*block_id).iter().for_each(|successor_id| {
            // all nodes added before, we can safely unwrap here
            graph.add_edge(
                *node_map.get(block_id).unwrap(),
                *node_map.get(successor_id).unwrap(),
                (),
            );
        })
    });

    // collect exit blocks
    let exit_blocks: Vec<BlockId> = blocks
        .into_iter()
        .filter(|block_id| cfg.successors(*block_id).is_empty())
        .collect();

    // if a basic block has no successors, it must be either
    //  1. a basic block ending with Ret, or
    //  2. a basic block ending with Abort
    debug_assert!(exit_blocks.iter().all(|block_id| {
        match &instructions[cfg.block_end(*block_id) as usize] {
            Bytecode::Ret(..) => true,
            Bytecode::Abort(..) => true,
            _ => false,
        }
    }));

    // Find the exit block or create an arbitrary block as the unified exit block
    // It is important to have a unified exit block for reverse-postorder DFS, as the one and only
    // exit block serves as a good starting point for the visitation algorithm.
    //
    // NOTE: given how BlockId are assigned, any number >= length of instructions: &[Bytecode] will
    // be safe to use as the BlockId for artificial blocks
    let exit_node = if exit_blocks.is_empty() {
        // if there are no exit blocks, it means that the whole CFG is a loop. In this case, we
        // create an arbitrary exit node and link all existing blocks to this exit node
        let unity_node = graph.add_node(instructions.len() as BlockId);
        for node_id in node_map.values() {
            graph.add_edge(*node_id, unity_node, ());
        }
        unity_node
    } else if exit_blocks.len() != 1 {
        // if more than one exit blocks are found, add an arbitrary unity block and link all exit
        // blocks to the unity block
        let unity_node = graph.add_node(instructions.len() as BlockId);
        for block_id in &exit_blocks {
            graph.add_edge(*node_map.get(block_id).unwrap(), unity_node, ());
        }
        unity_node
    } else {
        *node_map.get(exit_blocks.last().unwrap()).unwrap()
    };

    // done
    (graph, exit_node)
}

fn cfg_reverse_postorder_dfs(
    cfg: &StacklessControlFlowGraph,
    instructions: &[Bytecode],
) -> Vec<BlockId> {
    let mut result = vec![];

    // build and reverse the CFG
    let (mut graph, exit_node) = cfg_to_generic_graph(cfg, instructions);
    graph.reverse();

    // check that the exit_node now is the entry node after reversal
    debug_assert_eq!(
        graph
            .edges_directed(exit_node, EdgeDirection::Incoming)
            .count(),
        0
    );

    // Run postorder DFS visitation
    //
    // In reverse-postorder iteration, a node is visited before any of its successor nodes has been
    // visited, except when the successor is reached by a back edge.
    //
    // NOTE: reverse-postorder DFS is not the same as preorder
    let mut visitor = DfsPostOrder::new(&graph, exit_node);
    while let Some(node) = visitor.next(&graph) {
        let block_id = *graph.node_weight(node).unwrap();
        if block_id == instructions.len() as BlockId {
            // ignore the arbitrary unity block
            continue;
        }
        result.push(block_id);
    }

    // done
    result
}
