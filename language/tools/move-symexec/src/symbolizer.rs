// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::{bail, Result};
use log::{debug, warn};
use std::path::PathBuf;

use move_lang::{self, compiled_unit::CompiledUnit};
use vm::{file_format::CompiledScript, CompiledModule};

use crate::utils;

fn compile_modules(
    module_src: &[String],
    module_lib: &[String],
    move_output: &str,
) -> Result<Vec<CompiledModule>> {
    debug!("Compiling modules...");

    let path_interface_dir = utils::path_interface_dir(move_output)?;
    let (_, compiled_units) = move_lang::move_compile(
        module_src,
        module_lib,
        None,
        Some(path_interface_dir.into_os_string().into_string().unwrap()),
    )?;

    let mut compiled_modules = vec![];
    for unit in compiled_units {
        match unit {
            CompiledUnit::Script { loc, .. } => warn!(
                "Warning: found a script during module compilation: {}. \
                The script will not be involved in symbolic execution.",
                loc.file(),
            ),
            CompiledUnit::Module { module, .. } => {
                compiled_modules.push(module);
            }
        }
    }
    Ok(compiled_modules)
}

fn compile_script(
    script_file: &str,
    module_src: &[String],
    module_lib: &[String],
    move_output: &str,
) -> Result<CompiledScript> {
    debug!("Compiling script...");

    let path_interface_dir = utils::path_interface_dir(move_output)?;
    let (_, compiled_units) = move_lang::move_compile(
        &[script_file.to_owned()],
        [module_src, module_lib].concat().as_slice(),
        None,
        Some(path_interface_dir.into_os_string().into_string().unwrap()),
    )?;

    let mut compiled_script = None;
    for unit in compiled_units {
        match unit {
            CompiledUnit::Script { script, .. } => {
                if compiled_script.is_some() {
                    bail!("Error: found more than one script!");
                }
                compiled_script = Some(script);
            }
            CompiledUnit::Module { ident, .. } => warn!(
                "Warning: found a module during script compilation: {}. \
                The module will not be involved in symbolic execution.",
                ident,
            ),
        }
    }

    match compiled_script {
        None => bail!("Error: no scripts found!"),
        Some(script) => Ok(script),
    }
}

pub fn run(
    script_file: &str,
    move_src: &[String],
    move_lib: &[String],
    move_data: &str,
    move_output: &str,
    post_run_cleaning: bool,
) -> Result<()> {
    // preparation
    let path_move_data = PathBuf::from(move_data);
    let path_move_output = PathBuf::from(move_output);
    utils::maybe_recreate_dir(&path_move_data)?;
    utils::maybe_recreate_dir(&path_move_output)?;

    // compilation
    let lib_modules = compile_modules(move_lib, &[], move_output)?;
    debug!("{} lib modules compiled", lib_modules.len());

    let src_modules = compile_modules(move_src, move_lib, move_output)?;
    debug!("{} src modules compiled", src_modules.len());

    compile_script(script_file, move_src, move_lib, move_output)?;
    debug!("Script compiled");

    // cleaning
    if post_run_cleaning {
        utils::maybe_remove_dir(&path_move_data)?;
        utils::maybe_remove_dir(&path_move_output)?;
    }

    // done
    Ok(())
}
