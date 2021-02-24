// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use log::debug;

use move_core_types::language_storage::TypeTag;
use move_model::model::GlobalEnv;

use crate::worker::{MoveStatefulWorker, MoveWorker, MoveWorkerAttr};

/// Tag added to log messages
const LOG_TAG: &str = "[symeval]";

/// Attributes for a single-stage symbolizer
#[derive(Clone, Default)]
pub(crate) struct MoveSymbolizerAttr {}

impl MoveWorkerAttr for MoveSymbolizerAttr {}

/// A symbolizer worker that can symbolic Move programs
pub(crate) type MoveSymbolizer = MoveWorker<GlobalEnv, MoveSymbolizerAttr>;

impl MoveSymbolizer {
    pub fn symbolize(&self, _type_args: &[TypeTag]) -> Result<()> {
        // TODO: implement the logic
        debug!("{} Program symbolized", LOG_TAG);
        Ok(())
    }
}

/// A stateful controller to run multiple symbolization operations on Move programs
pub(crate) type MoveStatefulSymbolizer = MoveStatefulWorker<GlobalEnv, MoveSymbolizerAttr, ()>;

impl MoveStatefulSymbolizer {
    //
    // core operations
    //

    pub fn symbolize(&self, type_args: &[TypeTag]) -> Result<()> {
        self.top_worker().symbolize(type_args)
    }
}
