//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{Function, Module};
use crate::pass::*;

/// Manages running a set of passes over IR.
///
/// An important note is that this is actually a module pass itself, it's a pass
/// that simply runs other passes.
#[derive(Default)]
pub struct ModulePassManager {
    passes: Vec<Box<dyn ModuleTransformPass>>,
}

impl ModulePassManager {
    /// Creates a new, empty, module pass manager.
    pub fn new() -> Self {
        Self {
            passes: Vec::default(),
        }
    }

    /// Adds a transformation pass to the pass manager. This pass's order is defined
    /// relative to other calls to [`Self::add_pass`].
    pub fn add_pass<T: ModuleTransformPass + 'static>(&mut self, pass: T) {
        self.passes.push(Box::new(pass));
    }
}

impl ModuleTransformPass for ModulePassManager {
    fn run(&mut self, module: &mut Module, am: &ModuleAnalysisManager) -> PreservedAnalyses {
        let mut preserved = PreservedAnalyses::all();

        for pass in self.passes.iter_mut() {
            let other = pass.run(module, am);

            preserved = preserved.intersect(other)
        }

        preserved
    }
}

/// Manages running a set of passes over individual functions in the IR.
///
/// An important note is that this is actually a function pass itself, it's a pass
/// that simply runs other passes.
pub struct FunctionPassManager {
    passes: Vec<Box<dyn FunctionTransformPass>>,
}

impl FunctionTransformPass for FunctionPassManager {
    fn run(&mut self, func: &mut Function, am: &FunctionAnalysisManager) -> PreservedAnalyses {
        let mut preserved = PreservedAnalyses::all();

        for pass in self.passes.iter_mut() {
            let other = pass.run(func, am);

            preserved = preserved.intersect(other)
        }

        preserved
    }
}

/// Adapts a function transform pass to a module pass that runs the given
/// function pass over every function in the module.
///
/// This is mostly used when building the final pass pipeline.
pub struct FunctionToModulePassAdapter {
    pass: Box<dyn FunctionTransformPass + 'static>,
}

impl FunctionToModulePassAdapter {
    /// Adapts a given pass into a [`FunctionToModulePassAdapter`] that can then
    /// be used as a module pass.
    pub fn adapt<T: FunctionTransformPass + 'static>(pass: T) -> Self {
        Self {
            pass: Box::new(pass),
        }
    }
}

impl ModuleTransformPass for FunctionToModulePassAdapter {
    fn run(&mut self, module: &mut Module, am: &ModuleAnalysisManager) -> PreservedAnalyses {
        let fam = am.get::<FunctionAnalysisManagerModuleProxy>(module);
        let mut preserved = PreservedAnalyses::all();

        for func in module.functions() {
            let func = module.function_mut(func);
            let other = self.pass.run(func, &fam.borrow());

            preserved = preserved.intersect(other);
        }

        preserved
    }
}
