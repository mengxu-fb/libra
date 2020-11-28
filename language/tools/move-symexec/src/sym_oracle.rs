// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use once_cell::sync::OnceCell;
use std::{cmp, collections::HashMap};

use bytecode::{
    function_target::{FunctionTarget, FunctionTargetData},
    stackless_bytecode::Bytecode,
    stackless_bytecode_generator::StacklessBytecodeGenerator,
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId as ModuleIdByMove,
};
use spec_lang::env::{
    FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId as ModuleIdBySpec, StructEnv, StructId,
};

use crate::sym_filter::{collect_tracked_functions_and_script, FuncIdMatcher};

/// Lookup id for a `SymFuncInfo` in a `SymOracle`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct SymFuncId(usize);

/// Bridges and extends the `FunctionEnv` in move-prover
pub(crate) struct SymFuncInfo<'env> {
    func_id: SymFuncId,
    func_env: FunctionEnv<'env>,
    func_data: FunctionTargetData,
    func_cfg: StacklessControlFlowGraph,
    func_target: OnceCell<FunctionTarget<'env>>,
}

impl<'env> SymFuncInfo<'env> {
    fn new(func_id: SymFuncId, func_env: FunctionEnv<'env>) -> Self {
        // generate stackless bytecode
        let func_data = StacklessBytecodeGenerator::new(&func_env).generate_function();

        // generate control-flow graph
        let func_cfg = StacklessControlFlowGraph::new_forward(&func_data.code);
        debug_assert_eq!(func_cfg.entry_blocks().len(), 1);

        // done
        Self {
            func_id,
            func_env,
            func_data,
            func_cfg,
            func_target: OnceCell::new(),
        }
    }

    // getters
    pub fn get_context_string(&self) -> String {
        format!(
            "{}::{}::{}",
            self.func_env.module_env.self_address(),
            self.func_env.module_env.get_identifier(),
            self.func_env.get_identifier()
        )
    }

    pub fn get_instructions(&self) -> &[Bytecode] {
        &self.func_data.code
    }

    pub fn get_cfg(&self) -> &StacklessControlFlowGraph {
        &self.func_cfg
    }

    pub fn get_target(&'env self) -> &FunctionTarget<'env> {
        self.func_target
            .get_or_init(|| FunctionTarget::new(&self.func_env, &self.func_data))
    }
}

impl cmp::PartialEq for SymFuncInfo<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.func_id == other.func_id
    }
}

impl cmp::Eq for SymFuncInfo<'_> {}

/// Lookup id for a `SymStructInfo` in a `SymOracle`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
struct SymStructId(usize);

/// Bridges and extends the `StructEnv` in move-prover
pub(crate) struct SymStructInfo<'env> {
    struct_id: SymStructId,
    struct_env: StructEnv<'env>,
}

impl<'env> SymStructInfo<'env> {
    fn new(struct_id: SymStructId, struct_env: StructEnv<'env>) -> Self {
        Self {
            struct_id,
            struct_env,
        }
    }

    // getters
    pub fn get_context_string(&self) -> String {
        format!(
            "{}::{}::{}",
            self.struct_env.module_env.self_address(),
            self.struct_env.module_env.get_identifier(),
            self.struct_env.get_identifier()
        )
    }
}

impl cmp::PartialEq for SymStructInfo<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.struct_id == other.struct_id
    }
}

impl cmp::Eq for SymStructInfo<'_> {}

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
                tracked_functions.insert(sym_id, SymFuncInfo::new(sym_id.clone(), func_env));
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
                defined_structs.insert(sym_id, SymStructInfo::new(sym_id.clone(), struct_env));
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

    // lookup
    pub fn get_tracked_function_by_spec(
        &self,
        module_id: &ModuleIdBySpec,
        func_id: &FunId,
    ) -> Option<&SymFuncInfo<'env>> {
        self.tracked_functions_by_spec
            .get(module_id)
            .map(|funcs| funcs.get(func_id))
            .flatten()
            .map(|sym_id| self.tracked_functions.get(sym_id).unwrap())
    }

    pub fn get_tracked_function_by_move(
        &self,
        module_id: &ModuleIdByMove,
        func_id: &IdentStr,
    ) -> Option<&SymFuncInfo<'env>> {
        self.tracked_functions_by_move
            .get(module_id)
            .map(|funcs| funcs.get(func_id))
            .flatten()
            .map(|sym_id| self.tracked_functions.get(sym_id).unwrap())
    }

    pub fn get_defined_struct_by_spec(
        &self,
        module_id: &ModuleIdBySpec,
        struct_id: &StructId,
    ) -> Option<&SymStructInfo<'env>> {
        self.defined_structs_by_spec
            .get(module_id)
            .map(|funcs| funcs.get(struct_id))
            .flatten()
            .map(|sym_id| self.defined_structs.get(sym_id).unwrap())
    }

    pub fn get_defined_struct_by_move(
        &self,
        module_id: &ModuleIdByMove,
        struct_id: &IdentStr,
    ) -> Option<&SymStructInfo<'env>> {
        self.defined_structs_by_move
            .get(module_id)
            .map(|funcs| funcs.get(struct_id))
            .flatten()
            .map(|sym_id| self.defined_structs.get(sym_id).unwrap())
    }

    pub fn get_script_exec_unit(&self) -> &SymFuncInfo<'env> {
        // NOTE: we already checked that the `script_env` has one and only one function and that
        // function is always tracked. So both `unwrap`s are safe here
        self.get_tracked_function_by_spec(
            &self.script_env.get_id(),
            &self.script_env.get_functions().last().unwrap().get_id(),
        )
        .unwrap()
    }

    // misc
    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.len()
    }
}
