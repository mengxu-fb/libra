// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::{
    graph::{EdgeIndex, Graph, NodeIndex},
    visit::DfsPostOrder,
    EdgeDirection,
};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};

use bytecode_verifier::control_flow_graph::{BlockId, ControlFlowGraph, VMControlFlowGraph};
use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId,
};
use vm::{
    access::{ModuleAccess, ScriptAccess},
    file_format::{Bytecode, CodeOffset, CompiledModule, CompiledScript},
};

use crate::sym_setup::SymSetup;

/// The following classes aim for building an extended control-flow
/// graph that encloses both script and module CFGs, i.e., a super
/// graph that has CFGs connected by the call graph.

#[derive(Clone, Debug)]
enum CodeContext {
    Script,
    Module {
        module_id: ModuleId,
        function_id: Identifier,
    },
}

/// This is the basic block (i.e., the node) in the super-CFG.
type ExecBlockId = usize;

#[derive(Clone, Debug)]
struct ExecBlock {
    block_id: ExecBlockId,
    code_context: CodeContext,
    instructions: Vec<Bytecode>,
}

impl ExecBlock {
    pub fn new(block_id: ExecBlockId, code_context: CodeContext) -> Self {
        Self {
            block_id,
            code_context,
            instructions: vec![],
        }
    }

    pub fn add_instruction(&mut self, bytecode: Bytecode) {
        self.instructions.push(bytecode);
    }
}

/// This is the control flow (i.e., the edge) in the super-CFG.
type ExecFlowId = usize;

#[derive(Clone, Debug)]
enum ExecFlowType {
    /// Fall through: the next instruction is PC + 1
    Fallthrough,
    /// Conditional or unconditional (if condition is None) branch
    Branch {
        bytecode: Bytecode,
        condition: Option<bool>,
    },
    /// Function call
    Call { bytecode: Bytecode },
    /// Function return
    Ret,
}

#[derive(Clone, Debug)]
struct ExecFlow {
    flow_id: ExecFlowId,
    flow_type: ExecFlowType,
}

/// This is the super-CFG graph representation.
#[derive(Clone, Debug)]
pub(crate) struct ExecGraph {
    graph: Graph<ExecBlock, ExecFlow>,
    node_map: HashMap<ExecBlockId, NodeIndex>,
    edge_map: HashMap<ExecFlowId, EdgeIndex>,
    instruction_map: HashMap<CodeContext, HashMap<CodeOffset, (ExecBlockId, usize)>>,
}

impl ExecGraph {
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
            instruction_map: HashMap::new(),
        }
    }

    fn incorporate(
        &mut self,
        cfg: &VMControlFlowGraph,
        instructions: &[Bytecode],
        call_stack: &mut Vec<(CodeContext, CodeOffset)>,
        setup: &SymSetup,
        tracked_modules: &[CompiledModule],
    ) {
        // iterate script CFG
        for block_id in cfg_reverse_postorder_dfs(cfg, instructions) {
            // create the block
            let exec_block_id = self.graph.node_count();
            let mut exec_block = ExecBlock::new(exec_block_id, CodeContext::Script);

            // push instructions
            for offset in cfg.block_start(block_id)..=cfg.block_end(block_id) {
                let instruction = &instructions[offset as usize];
                match instruction {
                    Bytecode::Abort
                    | Bytecode::Branch(_)
                    | Bytecode::BrTrue(_)
                    | Bytecode::BrFalse(_)
                    | Bytecode::Ret => (),
                    _ => assert!(!instruction.is_branch()),
                };
            }

            // add block to graph
            let node_index = self.graph.add_node(exec_block);
            self.node_map.insert(exec_block_id, node_index);
        }
    }

    pub fn new(
        setup: &SymSetup,
        script: &CompiledScript,
        tracked_modules: &[CompiledModule],
    ) -> Self {
        // build CFG for the script
        let script_code = script.code();
        let script_cfg = VMControlFlowGraph::new(&script_code.code);

        // start symbolization from here
        let mut call_stack = vec![];
        let mut exec_graph = ExecGraph::empty();
        exec_graph.incorporate(
            &script_cfg,
            &script_code.code,
            &mut call_stack,
            setup,
            tracked_modules,
        );

        // TODO: to be removed
        cfg_reverse_postorder_dfs(&script_cfg, &script_code.code);
        for module in tracked_modules {
            let module_id = module.self_id();
            for func_def in module.function_defs() {
                let handle = module.function_handle_at(func_def.function);
                let func_id = module.identifier_at(handle.name);
                if !setup.is_function_tracked(&module_id, func_id) {
                    continue;
                }
                if let Some(code_unit) = &func_def.code {
                    let function_cfg = VMControlFlowGraph::new(&code_unit.code);
                    cfg_reverse_postorder_dfs(&function_cfg, &code_unit.code);
                }
            }
        }

        // done
        exec_graph
    }
}

// CFG / graph utils

/// Convert a CFG into generic graphs so we can benefit from various
/// graph algorithms, in particular, the DfsPostOrder visit algorithm,
/// in the petgraph crate.
fn cfg_to_generic_graph(
    cfg: &VMControlFlowGraph,
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

    // ensure there is only one unified exit
    let exit_blocks: Vec<BlockId> = blocks
        .into_iter()
        .filter(|block_id| cfg.successors(*block_id).is_empty())
        .collect();

    #[cfg(debug_assertions)]
    // if a basic block has no successors, it must be either
    //  1. a basic block ending with Ret
    //  2. a basic block ending with Abort
    for block_id in exit_blocks.iter() {
        match &instructions[cfg.block_end(*block_id) as usize] {
            Bytecode::Ret => true,
            Bytecode::Abort => false,
            _ => panic!("Invalid termination block in funciton CFG"),
        };
    }

    // If more than one exit blocks found, add an arbitrary unity block
    // and link all Ret blocks to the unity block.
    let exit_node = if exit_blocks.len() != 1 {
        // Note: given how BlockId are assigned, any number >= length of
        // instructions: &[Bytecode] will be safe to use as the BlockId
        // for artificial blocks
        let unity_node = graph.add_node(instructions.len() as BlockId);
        exit_blocks.iter().for_each(|block_id| {
            graph.add_edge(*node_map.get(block_id).unwrap(), unity_node, ());
        });
        unity_node
    } else {
        *node_map.get(exit_blocks.last().unwrap()).unwrap()
    };

    // done
    (graph, exit_node)
}

fn cfg_reverse_postorder_dfs(cfg: &VMControlFlowGraph, instructions: &[Bytecode]) -> Vec<BlockId> {
    let mut result = vec![];

    // build and reverse the CFG
    let (mut graph, exit_node) = cfg_to_generic_graph(cfg, instructions);
    graph.reverse();

    #[cfg(debug_assertions)]
    // check that the exit_node now is the entry node after reversal
    assert_eq!(
        graph
            .edges_directed(exit_node, EdgeDirection::Incoming)
            .count(),
        0
    );

    // Run post-order DFS visitation
    //
    // In reverse-postorder iteration, a node is visited before any of
    // its successor nodes has been visited, except when the successor
    // is reached by a back edge.
    // (Note that this is not the same as preorder.)
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
