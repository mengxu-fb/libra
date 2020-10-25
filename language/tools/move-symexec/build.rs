// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::{env, path::PathBuf, process::Command};

/// Default directory containing src
const CARGO_SRC: &str = "src";

/// Default directory containing deps
const CARGO_DEPS: &str = "deps";

/// Default directory containing the z3 package
const CARGO_DEPS_Z3: &str = "z3";

/// The include directory for z3
const Z3_INCLUDE_DIR: &str = "include";

/// The main header for z3 c library
const Z3_C_HEADER: &str = "z3.h";

/// The bin directory for z3
const Z3_BIN_DIR: &str = "bin";

/// The binding file
const CARGO_SRC_Z3_BINDINGS: &str = "bindings_z3.rs";

fn get_dep_if_missing(dep: &str) -> PathBuf {
    let dep_path: PathBuf = [env!("CARGO_MANIFEST_DIR"), CARGO_DEPS, dep]
        .iter()
        .collect();

    if !dep_path.exists() {
        let getter_script: PathBuf = [env!("CARGO_MANIFEST_DIR"), &format!("get-{}.sh", dep)]
            .iter()
            .collect();

        let status = Command::new(getter_script)
            .status()
            .unwrap_or_else(|_| panic!("Failed to run script: {:?}", dep_path));
        if !status.success() {
            panic!("Failed to get dependency: {}", dep);
        }
    }

    dep_path
}

fn handle_dep_z3() {
    // derive paths
    let z3_path = get_dep_if_missing(CARGO_DEPS_Z3);
    let z3_header_path = z3_path
        .join(Z3_INCLUDE_DIR)
        .join(Z3_C_HEADER)
        .into_os_string()
        .into_string()
        .unwrap();
    let z3_lib_path = z3_path
        .join(Z3_BIN_DIR)
        .into_os_string()
        .into_string()
        .unwrap();

    // generate bindings
    let bindings = bindgen::Builder::default()
        // The input header we would like to generate
        // bindings for.
        .header(z3_header_path)
        // Tell cargo to invalidate the built crate whenever any of the
        // included header files changed.
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    // output bindings
    let z3_bindings_output: PathBuf =
        [env!("CARGO_MANIFEST_DIR"), CARGO_SRC, CARGO_SRC_Z3_BINDINGS]
            .iter()
            .collect();
    bindings
        .write_to_file(z3_bindings_output)
        .expect("Couldn't write bindings!");

    // link against the z3 library
    println!("cargo:rustc-link-lib={}", CARGO_DEPS_Z3);
    println!("cargo:rustc-link-search=native={}", z3_lib_path);

    // pre-set the library path
    if cfg!(target_os = "macos") {
        println!("cargo:rustc-env=DYLD_FALLBACK_LIBRARY_PATH={}", z3_lib_path);
    } else if cfg!(target_os = "linux") {
        println!("cargo:rustc-env=LD_LIBRARY_PATH={}", z3_lib_path);
    } else {
        panic!("Currently only supported on MacOS and Linux");
    }
}

fn main() {
    handle_dep_z3();
}
