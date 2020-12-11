// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;
use std::collections::HashMap;

use spec_lang::env::{FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId};

// identifier matching
pub struct FuncIdMatcher {
    module_addr_regex: Regex,
    module_name_regex: Regex,
    func_name_regex: Regex,
}

impl FuncIdMatcher {
    pub fn new(expr: &str) -> Result<Self> {
        let tokens: Vec<&str> = expr.split("::").collect();
        if tokens.len() != 3 {
            bail!("Error: invalid match expression - {}", expr);
        }
        Ok(Self {
            module_addr_regex: Regex::new(tokens[0])?,
            module_name_regex: Regex::new(tokens[1])?,
            func_name_regex: Regex::new(tokens[2])?,
        })
    }

    fn is_match(&self, module_addr: &str, module_name: &str, func_name: &str) -> bool {
        self.module_addr_regex.is_match(module_addr)
            && self.module_name_regex.is_match(module_name)
            && self.func_name_regex.is_match(func_name)
    }
}

struct FuncIdMatcherList<'a> {
    matchers: Option<&'a [FuncIdMatcher]>,
}

impl FuncIdMatcherList<'_> {
    fn is_match(&self, module_addr: &str, module_name: &str, func_name: &str) -> bool {
        match &self.matchers {
            None => true,
            Some(matchers) => matchers
                .iter()
                .any(|m| m.is_match(module_addr, module_name, func_name)),
        }
    }
}

// identifier filtering
pub fn collect_tracked_functions_and_script<'env>(
    global_env: &'env GlobalEnv,
    inclusion: Option<&[FuncIdMatcher]>,
    exclusion: Option<&[FuncIdMatcher]>,
) -> (
    HashMap<ModuleId, HashMap<FunId, FunctionEnv<'env>>>,
    ModuleEnv<'env>,
) {
    // build filters
    let inc_matcher = FuncIdMatcherList {
        matchers: inclusion,
    };
    let exc_matcher = FuncIdMatcherList {
        matchers: exclusion,
    };

    // filter through the matchers
    let mut script_env = None;
    let mut module_map = HashMap::new();
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
        let module_key = module_env.get_name();
        let module_addr = format!("{:#X}", module_key.addr());
        let module_name = module_env.symbol_pool().string(module_key.name());
        let module_id = module_env.get_id();

        // iterate over the functions
        let mut func_map = HashMap::new();
        for func_env in module_env.into_functions() {
            // ignore native functions
            if func_env.is_native() {
                continue;
            }

            // check matches
            let func_name = func_env.symbol_pool().string(func_env.get_name());
            if script_mod // NOTE: the script main function is always tracked
                || (inc_matcher.is_match(&module_addr, &module_name, &func_name)
                    && !exc_matcher.is_match(&module_addr, &module_name, &func_name))
            {
                let exists = func_map.insert(func_env.get_id(), func_env);
                debug_assert!(exists.is_none());
            }
        }

        // add to module map
        let exists = module_map.insert(module_id, func_map);
        debug_assert!(exists.is_none());
    }

    // done
    (module_map, script_env.unwrap())
}
