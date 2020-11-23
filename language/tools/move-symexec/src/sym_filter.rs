// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;
use std::collections::{HashMap, HashSet};

use move_core_types::{identifier::IdentStr, language_storage::ModuleId};
use vm::{access::ModuleAccess, file_format::CompiledModule};

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

    fn is_match(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        self.module_addr_regex
            .is_match(&module_id.address().to_string())
            && self.module_name_regex.is_match(&module_id.name().as_str())
            && self.func_name_regex.is_match(func_id.as_str())
    }
}

struct FuncIdMatcherList<'a> {
    matchers: Option<&'a [FuncIdMatcher]>,
}

impl FuncIdMatcherList<'_> {
    fn is_match(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        match &self.matchers {
            None => true,
            Some(matchers) => matchers.iter().any(|m| m.is_match(module_id, func_id)),
        }
    }
}

// identifier filtering
pub fn collect_tracked_functions<'a>(
    tracked_modules: &[&'a CompiledModule],
    inclusion: Option<&[FuncIdMatcher]>,
    exclusion: Option<&[FuncIdMatcher]>,
) -> HashMap<ModuleId, HashSet<&'a IdentStr>> {
    // build filters
    let inc_matcher = FuncIdMatcherList {
        matchers: inclusion,
    };
    let exc_matcher = FuncIdMatcherList {
        matchers: exclusion,
    };

    // filter through the inclusion matchers
    let mut included_functions: HashMap<ModuleId, HashSet<&IdentStr>> = HashMap::new();
    for module in tracked_modules {
        let module_id = module.self_id();
        let func_set = module
            .function_defs()
            .iter()
            .filter_map(|func_def| {
                let handle = module.function_handle_at(func_def.function);
                let func_id = module.identifier_at(handle.name);
                if inc_matcher.is_match(&module_id, func_id) {
                    Some(func_id)
                } else {
                    None
                }
            })
            .collect();

        // ensure that we do not have duplicated modules
        let exists = included_functions.insert(module.self_id(), func_set);
        debug_assert!(exists.is_none());
    }

    // filter through the exclusion matchers
    let mut tracked_functions = HashMap::new();
    for (module_id, func_set) in included_functions.into_iter() {
        let filtered_set: HashSet<_> = func_set
            .into_iter()
            .filter(|func_id| !exc_matcher.is_match(&module_id, &func_id))
            .collect();

        if !filtered_set.is_empty() {
            let exists = tracked_functions.insert(module_id, filtered_set);
            debug_assert!(exists.is_none());
        }
    }

    // done
    tracked_functions
}
