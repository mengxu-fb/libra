// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use bytecode::{
    function_target::FunctionTargetData, stackless_bytecode_generator::StacklessBytecodeGenerator,
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use move_core_types::{identifier::Identifier, language_storage::ModuleId as ModuleIdByMove};
use spec_lang::env::{
    FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId as ModuleIdBySpec, StructEnv, StructId,
};

use crate::sym_filter::{collect_tracked_functions_and_script, FuncIdMatcher};

/// Lookup id for a `SymFuncInfo` in a `SymOracle`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct SymFuncId(usize);

/// Bridges and extends the `FunctionEnv` in move-prover
struct SymFuncInfo<'env> {
    func_env: FunctionEnv<'env>,
    func_data: FunctionTargetData,
    func_cfg: StacklessControlFlowGraph,
}

impl<'env> SymFuncInfo<'env> {
    fn new(func_env: FunctionEnv<'env>) -> Self {
        // generate stackless bytecode
        let func_data = StacklessBytecodeGenerator::new(&func_env).generate_function();

        // generate control-flow graph
        let func_cfg = StacklessControlFlowGraph::new_forward(&func_data.code);

        // done
        Self {
            func_env,
            func_data,
            func_cfg,
        }
    }
}

/// Lookup id for a `SymStructInfo` in a `SymOracle`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct SymStructId(usize);

/// Bridges and extends the `StructEnv` in move-prover
struct SymStructInfo<'env> {
    struct_env: StructEnv<'env>,
}

impl<'env> SymStructInfo<'env> {
    fn new(struct_env: StructEnv<'env>) -> Self {
        Self { struct_env }
    }
}

/// Bridges to the move-prover internals
pub(crate) struct SymOracle<'env> {
    global_env: &'env GlobalEnv,
    script_env: ModuleEnv<'env>,
    // tracked functions with two ways to look it up
    tracked_functions: HashMap<SymFuncId, SymFuncInfo<'env>>,
    tracked_functions_by_spec: HashMap<ModuleIdBySpec, HashMap<FunId, SymFuncId>>,
    tracked_functions_by_move: HashMap<ModuleIdByMove, HashMap<Identifier, SymFuncId>>,
    // defined structs with two ways to look it up
    defined_structs: HashMap<SymStructId, SymStructInfo<'env>>,
    defined_structs_by_spec: HashMap<ModuleIdBySpec, HashMap<StructId, SymStructId>>,
    defined_structs_by_move: HashMap<ModuleIdByMove, HashMap<Identifier, SymStructId>>,
}

impl<'env> SymOracle<'env> {
    pub fn new(
        global_env: &'env GlobalEnv,
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: &[FuncIdMatcher],
    ) -> Self {
        // collect tracked functions
        let (tracked_function_envs, script_env) =
            collect_tracked_functions_and_script(global_env, inclusion, Some(exclusion));

        // build per-function record
        let mut counter = 0;
        let mut tracked_functions = HashMap::new();
        let mut tracked_functions_by_spec = HashMap::new();
        let mut tracked_functions_by_move = HashMap::new();
        for (module_id, module_funcs) in tracked_function_envs {
            let mut module_funcs_by_spec = HashMap::new();
            let mut module_funcs_by_move = HashMap::new();
            for (func_id, func_env) in module_funcs {
                let sym_id = SymFuncId(counter);
                counter += 1;

                module_funcs_by_spec.insert(func_id, sym_id.clone());
                module_funcs_by_move.insert(func_env.get_identifier(), sym_id.clone());
                tracked_functions.insert(sym_id, SymFuncInfo::new(func_env));
            }
            // checks that each `Idenifier` is unique, should never fail
            debug_assert_eq!(module_funcs_by_spec.len(), module_funcs_by_move.len());

            let module_env = global_env.get_module(module_id);
            tracked_functions_by_spec.insert(module_id, module_funcs_by_spec);
            tracked_functions_by_move.insert(
                ModuleIdByMove::new(*module_env.self_address(), module_env.get_identifier()),
                module_funcs_by_move,
            );
        }
        // checks that each `ModuleIdByMove` is unique, should never fail
        debug_assert_eq!(
            tracked_functions_by_spec.len(),
            tracked_functions_by_move.len()
        );

        // collect all defined structs
        counter = 0;
        let mut defined_structs = HashMap::new();
        let mut defined_structs_by_spec = HashMap::new();
        let mut defined_structs_by_move = HashMap::new();
        for module_env in global_env.get_modules() {
            let module_id_by_spec = module_env.get_id();
            let module_id_by_move =
                ModuleIdByMove::new(*module_env.self_address(), module_env.get_identifier());

            let mut module_structs_by_spec = HashMap::new();
            let mut module_structs_by_move = HashMap::new();
            for struct_env in module_env.into_structs() {
                let sym_id = SymStructId(counter);
                counter += 1;

                module_structs_by_spec.insert(struct_env.get_id(), sym_id.clone());
                module_structs_by_move.insert(struct_env.get_identifier(), sym_id.clone());
                defined_structs.insert(sym_id, SymStructInfo::new(struct_env));
            }
            // checks that each `Idenifier` is unique, should never fail
            debug_assert_eq!(module_structs_by_spec.len(), module_structs_by_move.len());

            defined_structs_by_spec.insert(module_id_by_spec, module_structs_by_spec);
            defined_structs_by_move.insert(module_id_by_move, module_structs_by_move);
        }
        // checks that each `ModuleIdByMove` is unique, should never fail
        debug_assert_eq!(defined_structs_by_spec.len(), defined_structs_by_move.len());

        // done
        Self {
            global_env,
            script_env,
            tracked_functions,
            tracked_functions_by_spec,
            tracked_functions_by_move,
            defined_structs,
            defined_structs_by_spec,
            defined_structs_by_move,
        }
    }

    // misc
    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.len()
    }
}
