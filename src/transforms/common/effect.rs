//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{DataFlowGraph, Inst, InstData, Instruction, UnaryInst, Value};
use smallvec::SmallVec;

/// Checks whether a given instruction possibly has a side effect.
pub fn has_side_effect(dfg: &DataFlowGraph, inst: Inst) -> bool {
    match dfg.data(inst) {
        InstData::Load(load) => load.is_volatile(),
        InstData::Call(_)
        | InstData::IndirectCall(_)
        | InstData::Store(_)
        | InstData::Ret(_)
        | InstData::Br(_)
        | InstData::CondBr(_)
        | InstData::Unreachable(_) => true,
        _ => {
            // any instructions that may not have results should be covered above
            debug_assert_ne!(dfg.inst_to_result(inst), None);

            false
        }
    }
}
