//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{Function, Module};
use crate::passes::{FunctionAnalysisManager, ModuleAnalysisManager, PreservedAnalyses};

/// Models a pass that possibly performs a transformation over an entire SIR module.
///
/// While the pass may not actually modify the IR, it has the ability to, and needs to
/// declare what it changed (if anything) through [`PreservedAnalyses`](crate::passes::PreservedAnalyses).
pub trait ModuleTransformPass {
    ///
    ///
    ///
    ///
    fn run(&mut self, module: &mut Module, am: &ModuleAnalysisManager) -> PreservedAnalyses;
}

/// Defines a transformation over a single SIR function.
pub trait FunctionTransformPass {
    ///
    ///
    ///
    ///
    fn run(&mut self, func: &mut Function, am: &FunctionAnalysisManager) -> PreservedAnalyses;
}
