// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![macro_use]

use once_cell::sync::Lazy;
use std::{env, path::PathBuf};

/// A macro utility to get compile-time paths relative to the crate
#[macro_export]
macro_rules! crate_path {
    ($name:ident, $($item:expr),*) => {
        pub static $name: Lazy<PathBuf> = Lazy::new(
            || [env!("CARGO_MANIFEST_DIR") $(,$item)*].iter().collect()
        );
    }
}

// Path to the root of the project
crate_path!(PROJECT_ROOT, "..", "..", "..");

// Default path to directory containing nursery (source)
crate_path!(MOVE_LIBNURSERY, "..", "..", "diem-framework", "nursery");

// Default path to directory containing stdlib modules (source)
crate_path!(MOVE_STDLIB_MODULES, "..", "..", "diem-framework", "modules");

// Default path to directory containing diem scripts (source)
crate_path!(
    MOVE_DIEM_SCRIPTS,
    "..",
    "..",
    "diem-framework",
    "transaction_scripts"
);

/// A macro utility to get compile-time paths relative to the crate in String type
#[macro_export]
macro_rules! crate_path_string {
    ($name:ident, $($item:expr),*) => {
        static $name: Lazy<String> = Lazy::new(
            || [env!("CARGO_MANIFEST_DIR") $(,$item)*]
                .iter()
                .collect::<PathBuf>()
                .into_os_string()
                .into_string()
                .unwrap()
        );
    }
}

// Utilities for environment variables
pub fn read_env_var(v: &str) -> String {
    env::var(v).unwrap_or_else(|_| "".into()).to_uppercase()
}

pub fn read_env_var_bool(v: &str) -> bool {
    let val = read_env_var(v);
    val == "1" || val == "TRUE"
}

/// Switch for pretty printing in the outputs
const ENV_PRETTY: &str = "PRETTY";

pub fn is_in_pretty_mode() -> bool {
    read_env_var_bool(ENV_PRETTY)
}

/// Switch for using the on-disk workspace instead of the in-memory tmpfs
const ENV_WORKSPACE: &str = "WORKSPACE";

pub fn use_workspace() -> bool {
    read_env_var_bool(ENV_WORKSPACE)
}
