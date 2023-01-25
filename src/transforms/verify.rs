//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{ControlFlowGraph, DominatorTree};
use crate::ir::{Function, Module};
use crate::pass::{
    FunctionAnalysisManager, FunctionTransformPass, ModuleAnalysisManager, ModuleTransformPass,
    PreservedAnalyses,
};

/// Analysis pass that wraps the [`verify_module`] function.
///
/// This scans the entire module, and will do nothing if the module is valid. If
/// the module isn't valid, it will abort with an error.
pub struct VerifyModulePass;

impl ModuleTransformPass for VerifyModulePass {
    fn run(&mut self, _: &mut Module, _: &ModuleAnalysisManager) -> PreservedAnalyses {
        PreservedAnalyses::all()
    }
}

/// Analysis pass that wraps the [`verify_func`] function.
///
/// This scans the entire function, and will do nothing if the function is valid. If
/// the function isn't valid, it will abort with an error.
pub struct VerifyFunctionPass;

impl FunctionTransformPass for VerifyFunctionPass {
    fn run(&mut self, _: &mut Function, _: &FunctionAnalysisManager) -> PreservedAnalyses {
        PreservedAnalyses::all()
    }
}

/// Verifies that an entire module is valid SIR.
///
/// This checks that the SSA properties are upheld (dominance mainly), that
/// every block has a terminator, that every call is to a valid function, etc.
pub fn verify_module(_: &Module) -> Result<(), String> {
    todo!()
}

/// Verifies that a single function is a valid SIR function.
///
/// This checks that the SSA properties are upheld (dominance mainly), that
/// every block has a terminator, etc. If an error is found, that is returned.
pub fn verify_func(_: &Function) -> Result<(), String> {
    todo!()
}

fn verify_func_internal(_: &Function, _: &ControlFlowGraph, _: &DominatorTree) -> bool {
    todo!()
}
