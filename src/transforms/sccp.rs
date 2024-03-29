//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::Function;
use crate::pass::{FunctionAnalysisManager, FunctionTransformPass, PreservedAnalyses};

/// A Sparse Conditional Constant Propagation pass.
///
/// This uses the same constant folder internally as `InstSimplify`
pub struct SCCPPass;

impl FunctionTransformPass for SCCPPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        todo!()
    }
}
