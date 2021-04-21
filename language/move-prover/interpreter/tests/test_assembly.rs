// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{
    fs::{self, File},
    io::{self, Write},
    path::{Path, PathBuf},
};

use bytecode::{function_target_pipeline::FunctionTargetsHolder, pipeline_factory};
use bytecode_interpreter::assembly::{display::AstDebug, translate::translate};
use move_model::{model::GlobalEnv, run_model_builder};
use move_prover_test_utils::{baseline_test::verify_or_update_baseline, read_bool_env_var};

const ASM_EXP_EXTENSION: &str = "asm.exp";
const WORKDIR_EXTENSION: &str = "workdir";

fn prepare_workdir(path: &Path) -> io::Result<PathBuf> {
    let workdir = path.with_extension(WORKDIR_EXTENSION);
    if workdir.exists() {
        if workdir.is_dir() {
            fs::remove_dir_all(&workdir)?;
        } else {
            fs::remove_file(&workdir)?;
        }
    }
    fs::create_dir_all(&workdir)?;
    Ok(workdir)
}

fn stepwise_processing(
    env: &GlobalEnv,
    workdir: &Path,
    step: usize,
    name: &str,
    targets: &FunctionTargetsHolder,
) -> io::Result<()> {
    let filebase = workdir.join(format!("{}_{}", step, name));

    // dump the bytecode
    let mut text = String::new();
    for module_env in env.get_modules() {
        for func_env in module_env.get_functions() {
            for (variant, target) in targets.get_targets(&func_env) {
                if !target.data.code.is_empty() {
                    target.register_annotation_formatters_for_test();
                    text += &format!("\n[variant {}]\n{}\n", variant, target);
                }
            }
        }
    }
    let mut file = File::create(filebase.with_extension("bytecode"))?;
    file.write_all(text.as_bytes())?;

    // dump the assembly
    let assembly = translate(env, targets);
    let mut file = File::create(filebase.with_extension("asm"))?;
    file.write_all(assembly.print_ast().as_bytes())?;

    Ok(())
}

fn test_runner(path: &Path) -> datatest_stable::Result<()> {
    // create a workdir for dumping of needed
    let workdir_opt = if read_bool_env_var("DUMP") {
        Some(prepare_workdir(path)?)
    } else {
        None
    };

    // build the move model
    let srcs = vec![path.to_str().unwrap().to_string()];
    let env = run_model_builder(&srcs, &[])?;

    // short-circuit the test if there is any error
    assert!(!env.has_errors());
    assert!(!env.has_warnings());

    // create and process bytecode
    let mut targets = FunctionTargetsHolder::default();
    for module_env in env.get_modules() {
        for func_env in module_env.get_functions() {
            targets.add_target(&func_env)
        }
    }
    let pipeline = pipeline_factory::default_pipeline();
    match workdir_opt {
        None => pipeline.run(&env, &mut targets),
        Some(workdir) => pipeline.run_with_hook(
            &env,
            &mut targets,
            |holder| stepwise_processing(&env, &workdir, 0, "stackless", holder).unwrap(),
            |step, processor, holder| {
                stepwise_processing(&env, &workdir, step, &processor.name(), holder).unwrap()
            },
        ),
    }
    pipeline.run(&env, &mut targets);

    // translate and compare the assembly
    let assembly = translate(&env, &targets);
    let generated_asm = assembly.print_ast();
    verify_or_update_baseline(
        path.with_extension(ASM_EXP_EXTENSION).as_path(),
        &generated_asm,
    )?;
    Ok(())
}

datatest_stable::harness!(test_runner, "tests", r".*\.move");
