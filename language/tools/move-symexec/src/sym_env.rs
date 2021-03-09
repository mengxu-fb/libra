// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use bytecode::{
    borrow_analysis::BorrowAnalysisProcessor,
    clean_and_optimize::CleanAndOptimizeProcessor,
    data_invariant_instrumentation::DataInvariantInstrumentationProcessor,
    debug_instrumentation::DebugInstrumenter,
    eliminate_imm_refs::EliminateImmRefsProcessor,
    function_target::FunctionData,
    function_target_pipeline::{
        FunctionTargetPipeline, FunctionTargetsHolder, FunctionVariant,
        REGULAR_VERIFICATION_VARIANT,
    },
    global_invariant_instrumentation::GlobalInvariantInstrumentationProcessor,
    livevar_analysis::LiveVarAnalysisProcessor,
    loop_analysis::LoopAnalysisProcessor,
    memory_instrumentation::MemoryInstrumentationProcessor,
    mut_ref_instrumentation::MutRefInstrumenter,
    reaching_def_analysis::ReachingDefProcessor,
    spec_instrumentation::SpecInstrumentationProcessor,
    stackless_bytecode::Bytecode,
    stackless_control_flow_graph::StacklessControlFlowGraph,
    usage_analysis::UsageProcessor,
    verification_analysis::VerificationAnalysisProcessor,
};
use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId as ModuleIdByMove,
};
use move_model::model::{
    FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId as ModuleIdBySpec, StructEnv, StructId,
};

/// Lookup id for a `SymFuncInfo` in a `SymEnv`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct SymFuncId(usize);

/// Bridges and extends the `FunctionEnv` in move-model
pub(crate) struct SymFuncInfo<'env> {
    pub func_id: SymFuncId,
    pub func_env: FunctionEnv<'env>,
    pub func_data: FunctionData,
    pub func_cfg: StacklessControlFlowGraph,
}

impl<'env> SymFuncInfo<'env> {
    fn new(func_id: SymFuncId, func_env: FunctionEnv<'env>, func_data: FunctionData) -> Self {
        // generate control-flow graph
        let func_cfg = StacklessControlFlowGraph::new_forward(&func_data.code);
        Self {
            func_id,
            func_env,
            func_data,
            func_cfg,
        }
    }

    //
    // info
    //

    #[allow(unused)]
    pub fn context_string(&self) -> String {
        let module_env = &self.func_env.module_env;
        format!(
            "0x{}::{}::{}",
            module_env.self_address().short_str_lossless(),
            module_env.get_identifier(),
            self.func_env.get_identifier()
        )
    }

    #[allow(unused)]
    pub fn instructions(&self) -> &[Bytecode] {
        &self.func_data.code
    }

    #[allow(unused)]
    pub fn is_script_main(&self) -> bool {
        self.func_env.module_env.is_script_module()
    }
}

/// Lookup id for a `SymStructInfo` in a `SymEnv`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct SymStructId(usize);

/// Bridges and extends the `StructEnv` in move-model
pub(crate) struct SymStructInfo<'env> {
    pub struct_id: SymStructId,
    pub struct_env: StructEnv<'env>,
}

impl<'env> SymStructInfo<'env> {
    fn new(struct_id: SymStructId, struct_env: StructEnv<'env>) -> Self {
        Self {
            struct_id,
            struct_env,
        }
    }

    //
    // info
    //

    #[allow(unused)]
    pub fn context_string(&self) -> String {
        let module_env = &self.struct_env.module_env;
        format!(
            "0x{}::{}::{}",
            module_env.self_address().short_str_lossless(),
            module_env.get_identifier(),
            self.struct_env.get_identifier()
        )
    }
}

/// Bridges to the move-model/prover internals
pub(crate) struct SymEnv<'env> {
    #[allow(unused)]
    global_env: &'env GlobalEnv,
    // the module env representing the script
    script_env: ModuleEnv<'env>,
    // defined functions with two ways to look it up
    defined_functions: BTreeMap<SymFuncId, SymFuncInfo<'env>>,
    defined_functions_by_spec: BTreeMap<ModuleIdBySpec, BTreeMap<FunId, SymFuncId>>,
    defined_functions_by_move: BTreeMap<ModuleIdByMove, BTreeMap<Identifier, SymFuncId>>,
    // defined structs with two ways to look it up
    defined_structs: BTreeMap<SymStructId, SymStructInfo<'env>>,
    defined_structs_by_spec: BTreeMap<ModuleIdBySpec, BTreeMap<StructId, SymStructId>>,
    defined_structs_by_move: BTreeMap<ModuleIdByMove, BTreeMap<Identifier, SymStructId>>,
}

impl<'env> SymEnv<'env> {
    pub fn new(global_env: &'env GlobalEnv, no_pipeline: bool) -> Self {
        // collect tracked functions
        let (script_env, defined_function_envs) =
            Self::collect_defined_functions_and_script(global_env);

        // run prover passes
        let mut function_targets = Self::run_prover_passes(global_env, no_pipeline);

        // build per-function record
        let mut counter = 0;
        let mut defined_functions = BTreeMap::new();
        let mut defined_functions_by_spec = BTreeMap::new();
        let mut defined_functions_by_move = BTreeMap::new();
        for (module_id, module_funcs) in defined_function_envs {
            let mut module_funcs_by_spec = BTreeMap::new();
            let mut module_funcs_by_move = BTreeMap::new();
            for (func_id, func_env) in module_funcs {
                let sym_id = SymFuncId(counter);
                counter += 1;

                module_funcs_by_spec.insert(func_id, sym_id);
                module_funcs_by_move.insert(func_env.get_identifier(), sym_id);

                let func_data = function_targets.remove_target_data(
                    &func_env.get_qualified_id(),
                    FunctionVariant::Verification(REGULAR_VERIFICATION_VARIANT),
                );
                defined_functions.insert(sym_id, SymFuncInfo::new(sym_id, func_env, func_data));
            }
            // checks that each `Identifier` is unique, should never fail
            debug_assert_eq!(module_funcs_by_spec.len(), module_funcs_by_move.len());

            let module_env = global_env.get_module(module_id);
            defined_functions_by_spec.insert(module_id, module_funcs_by_spec);
            defined_functions_by_move.insert(
                ModuleIdByMove::new(*module_env.self_address(), module_env.get_identifier()),
                module_funcs_by_move,
            );
        }
        // checks that each `ModuleIdByMove` is unique, should never fail
        debug_assert_eq!(
            defined_functions_by_spec.len(),
            defined_functions_by_move.len()
        );

        // collect all defined structs
        counter = 0;
        let mut defined_structs = BTreeMap::new();
        let mut defined_structs_by_spec = BTreeMap::new();
        let mut defined_structs_by_move = BTreeMap::new();
        for module_env in global_env.get_modules() {
            let module_id_by_spec = module_env.get_id();
            let module_id_by_move =
                ModuleIdByMove::new(*module_env.self_address(), module_env.get_identifier());

            let mut module_structs_by_spec = BTreeMap::new();
            let mut module_structs_by_move = BTreeMap::new();
            for struct_env in module_env.into_structs() {
                let sym_id = SymStructId(counter);
                counter += 1;

                module_structs_by_spec.insert(struct_env.get_id(), sym_id);
                module_structs_by_move.insert(struct_env.get_identifier(), sym_id);
                defined_structs.insert(sym_id, SymStructInfo::new(sym_id, struct_env));
            }
            // checks that each `Identifier` is unique, should never fail
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
            defined_functions,
            defined_functions_by_spec,
            defined_functions_by_move,
            defined_structs,
            defined_structs_by_spec,
            defined_structs_by_move,
        }
    }

    //
    // Lookup
    //

    #[allow(unused)]
    pub fn get_function_by_spec(
        &self,
        module_id: &ModuleIdBySpec,
        func_id: &FunId,
    ) -> &SymFuncInfo<'env> {
        let sym_id = self
            .defined_functions_by_spec
            .get(module_id)
            .unwrap()
            .get(func_id)
            .unwrap();
        self.defined_functions.get(sym_id).unwrap()
    }

    #[allow(unused)]
    pub fn get_function_by_move(
        &self,
        module_id: &ModuleIdByMove,
        func_id: &IdentStr,
    ) -> &SymFuncInfo<'env> {
        let sym_id = self
            .defined_functions_by_move
            .get(module_id)
            .unwrap()
            .get(func_id)
            .unwrap();
        self.defined_functions.get(sym_id).unwrap()
    }

    #[allow(unused)]
    pub fn get_struct_by_spec(
        &self,
        module_id: &ModuleIdBySpec,
        struct_id: &StructId,
    ) -> &SymStructInfo<'env> {
        let sym_id = self
            .defined_structs_by_spec
            .get(module_id)
            .unwrap()
            .get(struct_id)
            .unwrap();
        self.defined_structs.get(sym_id).unwrap()
    }

    #[allow(unused)]
    pub fn get_defined_struct_by_move(
        &self,
        module_id: &ModuleIdByMove,
        struct_id: &IdentStr,
    ) -> &SymStructInfo<'env> {
        let sym_id = self
            .defined_structs_by_move
            .get(module_id)
            .unwrap()
            .get(struct_id)
            .unwrap();
        self.defined_structs.get(sym_id).unwrap()
    }

    #[allow(unused)]
    pub fn get_script_exec_unit(&self) -> &SymFuncInfo<'env> {
        // NOTE: we already checked that the `script_env` has one and only one function and that
        // function is always tracked. So both `unwrap`s are safe here
        self.get_function_by_spec(
            &self.script_env.get_id(),
            &self.script_env.get_functions().last().unwrap().get_id(),
        )
    }

    //
    // Misc
    //

    pub fn num_functions(&self) -> usize {
        self.defined_functions.len()
    }

    pub fn num_structs(&self) -> usize {
        self.defined_structs.len()
    }

    //
    // Utilities
    //

    fn collect_defined_functions_and_script(
        global_env: &'env GlobalEnv,
    ) -> (
        ModuleEnv<'env>,
        BTreeMap<ModuleIdBySpec, BTreeMap<FunId, FunctionEnv<'env>>>,
    ) {
        // filter through the matchers
        let mut script_env = None;
        let mut module_map = BTreeMap::new();
        for module_env in global_env.get_modules() {
            let script_mod = module_env.is_script_module();

            // found the script
            if script_mod {
                debug_assert_eq!(module_env.get_function_count(), 1);

                // ensure one and only one script
                debug_assert!(script_env.is_none());
                script_env = Some(module_env.clone());
            }

            // module basics
            let module_id = module_env.get_id();

            // iterate over the functions
            let mut func_map = BTreeMap::new();
            for func_env in module_env.into_functions() {
                if func_env.is_native() {
                    // ignore native functions
                    continue;
                }
                let exists = func_map.insert(func_env.get_id(), func_env);
                debug_assert!(exists.is_none());
            }

            // add to module map
            let exists = module_map.insert(module_id, func_map);
            debug_assert!(exists.is_none());
        }

        // done
        (script_env.unwrap(), module_map)
    }

    fn run_prover_passes(global_env: &GlobalEnv, no_pipeline: bool) -> FunctionTargetsHolder {
        // build the targets
        let mut targets = FunctionTargetsHolder::default();
        for module_env in global_env.get_modules() {
            for func_env in module_env.get_functions() {
                targets.add_target(&func_env)
            }
        }

        // build the pipeline
        // NOTE: keep the pipeline in-sync with
        //  - move-prover/src/pipelines.rs :: pipelines
        //  - move-prover/src/lib.rs :: create_bytecode_processing_pipeline
        let mut pipeline = FunctionTargetPipeline::default();
        if !no_pipeline {
            pipeline.add_processor(DebugInstrumenter::new());
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(BorrowAnalysisProcessor::new(true));
            pipeline.add_processor(MemoryInstrumentationProcessor::new());
            pipeline.add_processor(CleanAndOptimizeProcessor::new());
            pipeline.add_processor(UsageProcessor::new());
            pipeline.add_processor(VerificationAnalysisProcessor::new());
            pipeline.add_processor(LoopAnalysisProcessor::new());
            pipeline.add_processor(SpecInstrumentationProcessor::new());
            pipeline.add_processor(DataInvariantInstrumentationProcessor::new());
            pipeline.add_processor(GlobalInvariantInstrumentationProcessor::new());
        }

        // run the pipeline
        pipeline.run(global_env, &mut targets, None);
        targets
    }
}
