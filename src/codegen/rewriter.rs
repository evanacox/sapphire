//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaKey, SecondaryMap};
use crate::codegen::{
    Allocation, Architecture, MIRBlockInterval, MIRFunction, MachInst, ProgramPoint, SpillReload,
    StackFrame,
};

/// Performs the final phase of codegen, rewriting register-allocated x86-64
/// MIR to be fully valid x86-64 instructions that are ready to emit.
///
/// The main tasks being performed are these:
///
/// 1. Rewriting instructions to use hardware registers (based on register allocation)
/// 2. Emitting any necessary prologue/epilogue code
/// 3. Eliminating redundant `mov` instructions (e.g. `mov rax, rax`)
pub struct Rewriter {
    allocation: Allocation,
}

impl Rewriter {
    /// Creates a [`Rewriter`] that will rewrite a function using `allocation`.
    pub fn with_allocation(mut allocation: Allocation) -> Self {
        allocation.spills.sort_by_key(|(pp, _)| *pp);

        Self { allocation }
    }

    /// Rewrites a MIR function according to the allocation given in [`Self::with_allocation`].
    pub fn rewrite<Arch: Architecture>(
        self,
        function: &mut MIRFunction<Arch::Inst>,
        frame: &dyn StackFrame<Arch>,
    ) {
        let mut out = Vec::default();
        let mut spills = self.allocation.spills.iter().peekable();
        let mut block_intervals = SecondaryMap::default();
        let mut pp = ProgramPoint::key_new(0);
        let mut index = 0u32;
        let mut program_order_it = function.program_order().iter().peekable();

        while let Some(&block) = program_order_it.next() {
            let begin = index;

            // if this is the entry block, emit the prologue
            if function.program_order().first() == Some(&block) {
                let old = out.len();

                frame.generate_prologue(&mut out);

                // we just generated a bunch of instructions, need to include this in the first block.
                // we haven't emitted anything else before this, so doing `out.len` is fine
                index += (out.len() - old) as u32;
            }

            for &inst in function.block(block) {
                let rewrites = self.allocation.mapping.mapping_at(pp);
                let rewritten = inst.rewrite(rewrites, frame);

                // if we have any spills/reloads that are at this location, we need to emit them
                // before we emit the instruction. they will be in order from reg-alloc
                while spills.peek().is_some_and(move |(point, _)| *point == pp) {
                    let (_, spill) = spills.next().expect("we just checked .peek()");
                    let emit = match spill {
                        SpillReload::Spill { to, from } => Arch::Inst::store(8, *from, *to),
                        SpillReload::Reload { to, from } => Arch::Inst::load(8, *from, *to),
                    };

                    // we need to make sure to rewrite the store/load to make sure stack accesses
                    // are actually pointing at valid addresses
                    out.push(emit.rewrite(&[], frame));
                    index += 1;
                }

                // any return instruction needs the epilogue to be generated right before it
                if rewritten.is_ret() {
                    let old = out.len();

                    frame.generate_epilogue(&mut out);

                    index += (out.len() - old) as u32;
                }

                let mut skip = false;

                // if we have the following construction
                //
                //     jmp .L0
                // .L0:
                //
                // we want to not omit the jump, since it's completely useless
                if let Some(jmp) = rewritten.as_unconditional_jmp() {
                    if program_order_it
                        .peek()
                        .is_some_and(|&&block| block == jmp.to)
                    {
                        // skip actually emitting the jump, we can use fallthrough to get
                        // to the next block since it will be emitted next
                        skip = true;
                    }
                }

                // for any instruction `mov %r, %r` we want to not omit it
                if rewritten.is_nop_copy() {
                    skip = true;
                }

                if !skip {
                    out.push(rewritten);
                    index += 1;
                }

                pp = ProgramPoint::key_new(pp.key_index() + 1);
            }

            // update the block intervals, this will include the epilogue(s)
            block_intervals.insert(block, MIRBlockInterval::from_indices(begin, index));
        }

        function.rewrite_with(out, block_intervals);
    }
}
