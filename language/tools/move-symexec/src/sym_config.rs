// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use log::warn;
use regex::Regex;
use serde_json::{self, Value};
use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::BufReader,
    path::Path,
};

use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId,
};
use vm::{access::ModuleAccess, file_format::CompiledModule};

struct FuncIdMatcher {
    module_addr_regex: Regex,
    module_name_regex: Regex,
    func_name_regex: Regex,
}

impl FuncIdMatcher {
    fn new(expr: &str) -> Result<Self> {
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

struct FuncIdMatcherList {
    matchers_opt: Option<Vec<FuncIdMatcher>>,
}

impl FuncIdMatcherList {
    fn is_match(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        match &self.matchers_opt {
            None => true,
            Some(matchers) => matchers.iter().any(|m| m.is_match(module_id, func_id)),
        }
    }
}

pub(crate) struct SymConfig {
    tracked_functions: HashMap<ModuleId, HashSet<Identifier>>,
}

impl SymConfig {
    pub fn new(config_file: &str, src_modules: &[CompiledModule]) -> Result<Self> {
        let cfg_file = File::open(Path::new(config_file))?;
        let cfg_json: Value = serde_json::from_reader(BufReader::new(cfg_file))?;

        // handle inclusion
        let inc_matcher = match &cfg_json["inclusion"] {
            Value::Null => {
                // if no 'inclusion' set, include all functions that are defined
                FuncIdMatcherList { matchers_opt: None }
            }
            Value::Array(entries) => {
                // if 'inclusion' is explicitly defined, include modules and
                // functions that match the expression
                let mut matchers = Vec::new();
                for entry in entries {
                    if let Value::String(expr) = entry {
                        matchers.push(FuncIdMatcher::new(expr)?);
                    } else {
                        bail!(
                            "Error: invalid entry type in 'inclusion', all entries must be strings"
                        );
                    }
                }
                FuncIdMatcherList {
                    matchers_opt: Some(matchers),
                }
            }
            _ => bail!("Error: invalid config: 'inclusion' must be an array of strings"),
        };

        let mut included_functions: HashMap<ModuleId, HashSet<Identifier>> = HashMap::new();
        for module in src_modules {
            let module_id = module.self_id();
            let func_set = module
                .function_defs()
                .iter()
                .filter_map(|func_def| {
                    let handle = module.function_handle_at(func_def.function);
                    let func_id = module.identifier_at(handle.name);
                    if inc_matcher.is_match(&module_id, func_id) {
                        Some(func_id.to_owned())
                    } else {
                        None
                    }
                })
                .collect();

            if included_functions
                .insert(module.self_id(), func_set)
                .is_some()
            {
                warn!(
                    "Warning: duplication found in compiled modules: {}",
                    module.self_id()
                );
            }
        }

        // handle exclusion
        let exc_matcher = match &cfg_json["exclusion"] {
            Value::Null => {
                // if no 'exclusion' set, don't exclude anything
                FuncIdMatcherList {
                    matchers_opt: Some(Vec::new()),
                }
            }
            Value::Array(entries) => {
                // if 'exclusion' is explicitly defined, exclude modules and
                // functions that match the expression
                let mut matchers = Vec::new();
                for entry in entries {
                    if let Value::String(expr) = entry {
                        matchers.push(FuncIdMatcher::new(expr)?);
                    } else {
                        bail!(
                            "Error: invalid entry type in 'exclusion', all entries must be strings"
                        );
                    }
                }
                FuncIdMatcherList {
                    matchers_opt: Some(matchers),
                }
            }
            _ => bail!("Error: invalid config: 'exclusion' must be an array of strings"),
        };

        let mut tracked_functions = HashMap::new();
        for (module_id, func_set) in included_functions.into_iter() {
            let filtered_set: HashSet<Identifier> = func_set
                .into_iter()
                .filter(|func_id| !exc_matcher.is_match(&module_id, &func_id))
                .collect();

            if !filtered_set.is_empty() {
                tracked_functions.insert(module_id, filtered_set);
            }
        }

        Ok(Self { tracked_functions })
    }

    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.iter().map(|(_, v)| v.len()).sum()
    }
}
