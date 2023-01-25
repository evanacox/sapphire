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
use crate::pass::{FunctionAnalysisManager, ModuleAnalysisManager, PreservedAnalyses};

/// Models a pass that possibly performs a transformation over an entire SIR module.
///
/// While the pass may not actually modify the IR, it has the ability to, and needs to
/// declare what it changed (if anything) through [`PreservedAnalyses`](crate::pass::PreservedAnalyses).
pub trait ModuleTransformPass {
    /// Performs the transformation over a given SIR module.
    ///
    /// This function is expected to act as-if it was pure, i.e. calling the same
    /// pass multiple times on the same IR should produce equivalent IR each time
    /// and should return the same preserved analyses each time.
    fn run(&mut self, module: &mut Module, am: &ModuleAnalysisManager) -> PreservedAnalyses;
}

/// Defines a transformation over a single SIR function.
///
/// While the pass may not actually modify the IR, it has the ability to, and needs to
/// declare what it changed (if anything) through [`PreservedAnalyses`](crate::pass::PreservedAnalyses).
pub trait FunctionTransformPass {
    /// Performs the transformation over a given SIR function.
    ///
    /// This function is expected to act as-if it was pure, i.e. calling the same
    /// pass multiple times on the same IR should produce equivalent IR each time
    /// and should return the same preserved analyses each time.
    fn run(&mut self, func: &mut Function, am: &FunctionAnalysisManager) -> PreservedAnalyses;
}
