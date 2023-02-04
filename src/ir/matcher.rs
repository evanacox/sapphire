//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::*;
use std::marker::PhantomData;

/// A basic matcher for a single value/instruction in the IR.
pub trait IRMatcher<'a> {
    /// Runs the matcher against a given instruction. Returns whether
    /// or not the value was matched.
    fn matches_inst(self, inst: Inst, dfg: &'a DataFlowGraph) -> bool;

    /// Runs the matcher against a given value. Returns whether
    /// or not the value was matched.  
    fn matches_val(self, val: Value, dfg: &'a DataFlowGraph) -> bool;
}

/// A matcher that wraps up a matcher function.
pub struct BasicInstMatcher<'a, F>
where
    F: FnOnce(Inst, &'a DataFlowGraph) -> bool + 'a,
{
    matcher: F,
    data: PhantomData<&'a i32>,
}

impl<'a, F> IRMatcher<'a> for BasicInstMatcher<'a, F>
where
    F: FnOnce(Inst, &'a DataFlowGraph) -> bool,
{
    fn matches_inst(self, inst: Inst, dfg: &'a DataFlowGraph) -> bool {
        (self.matcher)(inst, dfg)
    }

    fn matches_val(self, val: Value, dfg: &'a DataFlowGraph) -> bool {
        match dfg.value_to_inst(val) {
            Some(inst) => self.matches_inst(inst, dfg),
            None => false,
        }
    }
}

/// A matcher that matches a binary instruction.
pub fn binary<'a>(out: &'a mut Option<&'a (dyn BinaryInst + 'a)>) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: |inst, dfg| {
            *out = match dfg.data(inst) {
                InstData::ICmp(inst) => Some(inst),
                InstData::FCmp(inst) => Some(inst),
                InstData::And(inst) => Some(inst),
                InstData::Or(inst) => Some(inst),
                InstData::Xor(inst) => Some(inst),
                InstData::Shl(inst) => Some(inst),
                InstData::AShr(inst) => Some(inst),
                InstData::LShr(inst) => Some(inst),
                InstData::IAdd(inst) => Some(inst),
                InstData::ISub(inst) => Some(inst),
                InstData::IMul(inst) => Some(inst),
                InstData::SDiv(inst) => Some(inst),
                InstData::UDiv(inst) => Some(inst),
                InstData::SRem(inst) => Some(inst),
                InstData::URem(inst) => Some(inst),
                InstData::FAdd(inst) => Some(inst),
                InstData::FSub(inst) => Some(inst),
                InstData::FMul(inst) => Some(inst),
                InstData::FDiv(inst) => Some(inst),
                InstData::FRem(inst) => Some(inst),
                _ => None,
            };

            out.is_some()
        },
        data: PhantomData::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_matchers() {
        let mut module = Module::new("test");
        let mut b = module.define_function("test", SigBuilder::new().build());

        let bb0 = b.create_block("bb0");
        b.switch_to(bb0);

        let v0 = b.append().iconst(Type::i32(), 42, DebugInfo::fake());
        let v1 = b.append().iconst(Type::i32(), 6, DebugInfo::fake());
        let v2 = b.append().iadd(v0, v1, DebugInfo::fake());

        let f = b.define();
        let func = module.function_mut(f);
        let mut cursor = FuncCursor::over(func);

        fn print_if_matches(v: Value, cursor: &mut FuncCursor<'_>) {
            let mut out = None;
            let matcher = binary(&mut out);

            assert!(matcher.matches_val(v, cursor.dfg()));
        }

        print_if_matches(v2, &mut cursor);
    }
}
