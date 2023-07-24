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

/// A control-flow graph simplification pass.
///
/// Performs the following simplifications:
///
/// 1. Removes blocks with no predecessors
/// 2. Eliminates blocks that only contain an unconditional branch
/// 3. Eliminates φ nodes for blocks with a single predecessor
/// 4. Merges blocks into their predecessors if they only have one predecessor
///    and their predecessor only has one successor
pub struct SimplifyCFGPass;

impl FunctionTransformPass for SimplifyCFGPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
       todo!()
    }
}