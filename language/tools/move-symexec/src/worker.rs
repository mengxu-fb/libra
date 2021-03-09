// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::{
    fs,
    path::{Path, PathBuf},
    rc::Rc,
};

use crate::utils::PathToString;

/// Subdirectory in `storage_dir/` where the fs-backed attribute for this worker lives
const WORKDIR: &str = "workdir";

/// Subdirectory in `storage_dir/` where the storage dir of this worker's dependents reside
const PLAYDIR: &str = "playdir";

/// Indicate whether the parent of the worker is another worker or the root information
pub(crate) enum Parent<I, A: MoveWorkerAttr> {
    Info(I),
    Worker(Rc<MoveWorker<I, A>>),
}

/// Holds attributes of the worker
pub(crate) trait MoveWorkerAttr: Default + Clone {}

/// A worker instance with the knowledge of its parent
pub(crate) struct MoveWorker<I, A: MoveWorkerAttr> {
    workdir: PathBuf,
    playdir: PathBuf,
    attr: A,
    parent: Parent<I, A>,
}

impl<I, A: MoveWorkerAttr> MoveWorker<I, A> {
    pub fn new<P: AsRef<Path>>(storage_dir: P, parent: Parent<I, A>) -> Result<Self> {
        // create storage layout
        if fs::read_dir(storage_dir.as_ref())?.next().is_some() {
            bail!("Storage is not empty: {}", storage_dir.path_to_string()?);
        }
        let workdir = storage_dir.as_ref().join(WORKDIR);
        fs::create_dir(&workdir)?;
        let playdir = storage_dir.as_ref().join(PLAYDIR);
        fs::create_dir(&playdir)?;

        // init or inherit
        let attr = match &parent {
            Parent::Info(_) => A::default(),
            Parent::Worker(p) => p.attr.clone(),
        };

        Ok(Self {
            workdir,
            playdir,
            attr,
            parent,
        })
    }

    #[allow(unused)]
    pub fn workdir(&self) -> &Path {
        &self.workdir
    }

    pub fn playdir(&self) -> &Path {
        &self.playdir
    }

    pub fn attr(&self) -> &A {
        &self.attr
    }

    pub fn attr_mut(&mut self) -> &mut A {
        &mut self.attr
    }

    pub fn info(&self) -> &I {
        match &self.parent {
            Parent::Worker(p) => p.info(),
            Parent::Info(info) => info,
        }
    }
}

/// Holds the current worker state
struct OpState<I, A: MoveWorkerAttr, D: Default> {
    worker: Rc<MoveWorker<I, A>>,
    data: D,
}

impl<I, A: MoveWorkerAttr, D: Default> OpState<I, A, D> {
    pub fn new(workdir: PathBuf, parent: Parent<I, A>) -> Result<Self> {
        fs::create_dir(&workdir)?;
        Ok(Self {
            worker: Rc::new(MoveWorker::new(workdir, parent)?),
            data: D::default(),
        })
    }
}

/// A stateful controller to run multiple operations on Move programs
pub(crate) struct MoveStatefulWorker<I, A: MoveWorkerAttr, D: Default> {
    workdir: PathBuf,
    op_stack: Vec<OpState<I, A, D>>,
    num_contexts: usize,
}

impl<I, A: MoveWorkerAttr, D: Default> MoveStatefulWorker<I, A, D> {
    /// Create a new stateful worker, assuming that `workdir` is already created
    pub fn new(workdir: PathBuf, info: I) -> Result<Self> {
        // create the initial states
        let state = OpState::new(workdir.join("0"), Parent::Info(info))?;

        // done
        Ok(Self {
            workdir,
            op_stack: vec![state],
            num_contexts: 1,
        })
    }

    //
    // stack operations
    //

    fn get_state(&self) -> &OpState<I, A, D> {
        self.op_stack.last().expect("Stack should never be empty")
    }

    fn get_state_mut(&mut self) -> &mut OpState<I, A, D> {
        self.op_stack
            .last_mut()
            .expect("Stack should never be empty")
    }

    pub fn top_mut(&mut self) -> (&mut MoveWorker<I, A>, &mut D) {
        let top = self.get_state_mut();
        (
            Rc::get_mut(&mut top.worker).expect("Only the stack-top worker can be used"),
            &mut top.data,
        )
    }

    pub fn top_worker(&self) -> Rc<MoveWorker<I, A>> {
        Rc::clone(&self.get_state().worker)
    }

    pub fn top_attr(&self) -> &A {
        self.get_state().worker.attr()
    }

    pub fn top_data(&self) -> &D {
        &self.get_state().data
    }

    pub fn iter_data(&self) -> impl Iterator<Item = &D> {
        self.op_stack.iter().map(|state| &state.data)
    }

    pub fn push(&mut self) -> Result<()> {
        let old_state = self.get_state();
        let new_state = OpState::new(
            self.workdir.join(self.num_contexts.to_string()),
            Parent::Worker(Rc::clone(&old_state.worker)),
        )?;

        self.op_stack.push(new_state);
        self.num_contexts += 1;
        Ok(())
    }

    pub fn pop(&mut self) -> Result<()> {
        if self.op_stack.len() == 1 {
            bail!("Cannot have more pops than pushes");
        }
        let state = self.op_stack.pop().unwrap();
        if Rc::try_unwrap(state.worker).is_err() {
            bail!("Found dangling references to a popped worker");
        }
        Ok(())
    }

    pub fn balanced(&self) -> bool {
        self.op_stack.len() == 1
    }
}
