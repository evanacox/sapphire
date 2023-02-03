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

/// Checks if a given instruction could possibly cause a pointer
/// to escape.
///
/// Currently, any branches, calls, loads/stores/offsets
pub fn could_cause_pointer_escape(dfg: &DataFlowGraph, inst: Inst) -> bool {
    matches!(
        dfg.data(inst),
        InstData::Call(_)
            | InstData::IndirectCall(_)
            | InstData::Store(_)
            | InstData::PToI(_)
            | InstData::Ret(_)
            | InstData::Br(_)
            | InstData::CondBr(_)
    )
}

/// Looks at an instruction and returns any of its pointer operands that are
/// considered to have "escaped" the function's control.
///
/// Notable limitations right now are that if a pointer goes into a φ node
/// at all it is considered to be leaked.
pub fn pointer_escapees(dfg: &DataFlowGraph, inst: Inst) -> SmallVec<[Value; 4]> {
    let mut escapees = SmallVec::default();

    match dfg.data(inst) {
        InstData::Call(call) => escapees.extend(
            call.operands()
                .iter()
                .copied()
                .filter(|val| dfg.ty(*val).is_ptr()),
        ),
        InstData::IndirectCall(call) => escapees.extend(
            call.operands()
                .iter()
                .copied()
                .filter(|val| dfg.ty(*val).is_ptr()),
        ),
        InstData::Store(store) => {
            if dfg.ty(store.stored()).is_ptr() {
                escapees.push(store.stored())
            }
        }
        InstData::PToI(cast) => escapees.push(cast.operand()),
        InstData::Ret(ret) => {
            if let Some(val) = ret.value() {
                if dfg.ty(val).is_ptr() {
                    escapees.push(val);
                }
            }
        }
        InstData::Br(br) => escapees.extend(
            br.target()
                .args()
                .iter()
                .copied()
                .filter(|val| dfg.ty(*val).is_ptr()),
        ),
        InstData::CondBr(condbr) => escapees.extend(
            condbr
                .operands()
                .iter()
                .copied()
                .filter(|val| dfg.ty(*val).is_ptr()),
        ),
        _ => {}
    }

    escapees
}
