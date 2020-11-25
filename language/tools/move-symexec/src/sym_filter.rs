// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;

use spec_lang::env::{FunctionEnv, GlobalEnv};

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
pub fn collect_tracked_functions<'env>(
    global_env: &'env GlobalEnv,
    inclusion: Option<&[FuncIdMatcher]>,
    exclusion: Option<&[FuncIdMatcher]>,
) -> Vec<FunctionEnv<'env>> {
    // build filters
    let inc_matcher = FuncIdMatcherList {
        matchers: inclusion,
    };
    let exc_matcher = FuncIdMatcherList {
        matchers: exclusion,
    };

    // filter through the matchers
    let mut functions = vec![];
    for module_env in global_env.get_modules() {
        let module_id = module_env.get_name();
        let module_addr = format!("{:#X}", module_id.addr());
        let module_name = module_env.symbol_pool().string(module_id.name());

        // iterate over the functions
        for func_env in module_env.clone().into_functions() {
            let func_name = func_env.symbol_pool().string(func_env.get_name());
            if inc_matcher.is_match(&module_addr, &module_name, &func_name)
                && !exc_matcher.is_match(&module_addr, &module_name, &func_name)
            {
                functions.push(func_env);
            }
        }
    }

    // done
    functions
}
