// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use bytecode::{
    function_target::FunctionTargetData, stackless_bytecode_generator::StacklessBytecodeGenerator,
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use spec_lang::env::{FunId, FunctionEnv, GlobalEnv, ModuleId};

use crate::sym_filter::{collect_tracked_functions, FuncIdMatcher};

/// Bridges and extends the `FunctionEnv` in move-prover
struct SymFuncRecord<'env> {
    func_env: FunctionEnv<'env>,
    func_data: FunctionTargetData,
    func_cfg: StacklessControlFlowGraph,
}

impl<'env> SymFuncRecord<'env> {
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

/// Bridges to the move-prover internals
pub(crate) struct SymOracle<'env> {
    global_env: &'env GlobalEnv,
    tracked_functions: HashMap<ModuleId, HashMap<FunId, SymFuncRecord<'env>>>,
}

impl<'env> SymOracle<'env> {
    pub fn new(
        global_env: &'env GlobalEnv,
        inclusion: Option<&[FuncIdMatcher]>,
        exclusion: &[FuncIdMatcher],
    ) -> Self {
        // collect tracked functions
        let tracked_function_envs =
            collect_tracked_functions(global_env, inclusion, Some(exclusion));

        // build per-function record
        let tracked_functions = tracked_function_envs
            .into_iter()
            .map(|(module_id, module_funcs)| {
                (
                    module_id,
                    module_funcs
                        .into_iter()
                        .map(|(func_id, func_env)| (func_id, SymFuncRecord::new(func_env)))
                        .collect(),
                )
            })
            .collect();

        // done
        Self {
            global_env,
            tracked_functions,
        }
    }

    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.values().flatten().count()
    }
}
