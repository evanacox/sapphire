//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! This module defines SIR matchers that can be used inside of instruction
//! selection code.
//!
//! These matchers are not meant to be used in optimization passes, see the
//! [`matchers`](ir::matchers) module for those. These are meant
//! to work with [`codegen`](crate::codegen) infrastructure.

//
// This file is an absolute mess but the API exposed is relatively nice.
//
// All of the constant #[inline(always)] hints are there for a reason, the performance
// of this mess will be atrocious without inlining to turn it into a bunch of
// array accesses and `cmp`s (which is all it is under the hood, lookups into the IR
// and checks on enum variants). There isn't actually any dynamic lookups going on anywhere,
// meaning that theoretically this can all be inlined very well.
//
// My dearest apologies if you're trying to understand this, my best advice
// would be to try to understand the matchers in src/ir/matchers.rs first
// before coming back to this one. This is a logical extension of the idea
// in the other matcher file, so if you already understand how that one works
// reasonably well you'll be much better suited to understand this.
//

use crate::codegen::*;
use crate::ir;
use crate::ir::{BinaryInst, FunctionDefinition, ICmpOp, InstData, Instruction, Value};
use paste::paste;
use std::cell::RefCell;
use std::marker::PhantomData;

/// A basic matcher for a single instruction, for use in merging during instruction selection.
///
/// This uses the checks inside the [`LoweringContext`] to
/// see not only if the IR matches the pattern, but to see if the match is able to be
/// merged.
pub trait ISelMergeMatcher<Arch>
where
    Arch: Architecture,
{
    /// Runs the matcher against an instruction, the instruction as treated as the **base**
    /// of the merge (and is thus not subject to the requirements in [`LoweringContext::able_to_merge_with`]).
    ///
    /// All of the operands of `base` (that are matched on) are subject to the requirements.
    fn matches_as_base(&self, base: ir::Inst, ctx: FramelessCtx<'_, '_, '_, Arch>) -> bool;

    /// Runs the matcher against `val`, the instruction as treated as an **operand** of the merge and
    /// is checked against `base` using [`LoweringContext::able_to_merge_with`].
    ///
    /// All of the operands of `val` (that are matched on) are also subject to the requirements.
    fn matches_as_operand(
        &self,
        val: Value,
        base: ir::Inst,
        ctx: FramelessCtx<'_, '_, '_, Arch>,
    ) -> bool;

    /// Once [`Self::matches_as_base`] has been called and returns `true`, this can be used
    /// to actually go update the state of the [`LoweringContext`] and mark that each matched
    /// operand is going to be merged with `base`
    fn mark_as_merged_base(&self, base: ir::Inst, ctx: FramelessCtx<'_, '_, '_, Arch>);

    /// Once [`Self::matches_as_operand`] has been called and returns `true`, this can be used
    /// to actually go update the state of the [`LoweringContext`] and mark that each matched
    /// instruction is going to be merged with `base`
    fn mark_as_merged_operand(
        &self,
        val: Value,
        base: ir::Inst,
        ctx: FramelessCtx<'_, '_, '_, Arch>,
    );
}

/// Performs the two-step "check if able to merge" and "mark the merge as done" process in one step.
///
/// This is the preferred way to match on patterns when work between the two steps isn't needed.
#[inline(always)]
pub fn merge_if_matches<Arch, Matcher>(
    base: ir::Inst,
    (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
    matcher: Matcher,
) -> bool
where
    Arch: Architecture,
    Matcher: ISelMergeMatcher<Arch>,
{
    if matcher.matches_as_base(base, (def, ctx)) {
        matcher.mark_as_merged_base(base, (def, ctx));

        true
    } else {
        false
    }
}

/// Performs the two-step "check if able to merge" and "mark the merge as done" process in one step.
///
/// This is the preferred way to match on patterns when work between the two steps isn't needed.
#[inline(always)]
pub fn merge_if_matches_operand<Arch, Matcher>(
    val: Value,
    base: ir::Inst,
    (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
    matcher: Matcher,
) -> bool
where
    Arch: Architecture,
    Matcher: ISelMergeMatcher<Arch>,
{
    if matcher.matches_as_operand(val, base, (def, ctx)) {
        matcher.mark_as_merged_operand(val, base, (def, ctx));

        true
    } else {
        false
    }
}

/// Used when you want to check if a merge between `base` and its operands is safe, this
/// must be followed by a [`mark_merged`] to actually complete the merge.
///
/// Usually you don't want this, use the single step [`merge_if_matches_operand`] instead unless
/// you specifically need to run additional checks outside the pattern syntax.
#[inline(always)]
pub fn matches<Arch, Matcher>(
    base: ir::Inst,
    ctx: FramelessCtx<'_, '_, '_, Arch>,
    matcher: &Matcher,
) -> bool
where
    Arch: Architecture,
    Matcher: ISelMergeMatcher<Arch>,
{
    matcher.matches_as_base(base, ctx)
}

/// Used when you want to check if a merge between `base` and its operands is safe, this
/// must be followed by a [`mark_merged_operand`] to actually complete the merge.
///
/// Usually you don't want this, use the single step [`merge_if_matches_operand`] instead unless
/// you specifically need to run additional checks outside the pattern syntax.
#[inline(always)]
pub fn matches_operand<Arch, Matcher>(
    val: Value,
    base: ir::Inst,
    ctx: FramelessCtx<'_, '_, '_, Arch>,
    matcher: &Matcher,
) -> bool
where
    Arch: Architecture,
    Matcher: ISelMergeMatcher<Arch>,
{
    matcher.matches_as_operand(val, base, ctx)
}

/// Used when you want to actually perform the merge between `base` and its operands after
/// successfully matching via [`matches()`].
///
/// Usually you don't want this, use the single step [`merge_if_matches`] instead unless
/// you specifically need to run additional checks outside the pattern syntax.
#[inline(always)]
pub fn mark_merged<Arch, Matcher>(
    base: ir::Inst,
    ctx: FramelessCtx<'_, '_, '_, Arch>,
    matcher: &Matcher,
) where
    Arch: Architecture,
    Matcher: ISelMergeMatcher<Arch>,
{
    matcher.mark_as_merged_base(base, ctx);
}

/// Used when you want to actually perform the merge onto `base` with the operand `val` after
/// successfully matching via [`matches_operand`].
///
/// Usually you don't want this, use the single step [`merge_if_matches_operand`] instead unless
/// you specifically need to run additional checks outside the pattern syntax.
#[inline(always)]
pub fn mark_merged_operand<Arch, Matcher>(
    val: Value,
    base: ir::Inst,
    ctx: FramelessCtx<'_, '_, '_, Arch>,
    matcher: &Matcher,
) where
    Arch: Architecture,
    Matcher: ISelMergeMatcher<Arch>,
{
    matcher.mark_as_merged_operand(val, base, ctx);
}

/// A matcher that wraps up a matcher function.
pub struct BasicISelMergeMatcher<Arch, F1, F2, F3, F4>
where
    Arch: Architecture,
    F1: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool,
    F2: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool,
    F3: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>),
    F4: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>),
{
    base_matcher: F1,
    operand_matcher: F2,
    base_merger: F3,
    operand_merger: F4,
    _unused: PhantomData<fn() -> Arch>,
}

impl<Arch, F1, F2, F3, F4> Clone for BasicISelMergeMatcher<Arch, F1, F2, F3, F4>
where
    Arch: Architecture,
    F1: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool + Clone,
    F2: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool + Clone,
    F3: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>) + Clone,
    F4: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>) + Clone,
{
    fn clone(&self) -> Self {
        Self {
            base_matcher: self.base_matcher.clone(),
            operand_matcher: self.operand_matcher.clone(),
            base_merger: self.base_merger.clone(),
            operand_merger: self.operand_merger.clone(),
            _unused: PhantomData,
        }
    }
}

impl<Arch, F1, F2, F3, F4> Copy for BasicISelMergeMatcher<Arch, F1, F2, F3, F4>
where
    Arch: Architecture,
    F1: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool + Copy,
    F2: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool + Copy,
    F3: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>) + Copy,
    F4: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>) + Copy,
{
}

impl<Arch, F1, F2, F3, F4> ISelMergeMatcher<Arch> for BasicISelMergeMatcher<Arch, F1, F2, F3, F4>
where
    Arch: Architecture,
    F1: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool,
    F2: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>) -> bool,
    F3: Fn(ir::Inst, FramelessCtx<'_, '_, '_, Arch>),
    F4: Fn(ir::Inst, ir::Inst, FramelessCtx<'_, '_, '_, Arch>),
{
    #[inline(always)]
    fn matches_as_base(&self, base: ir::Inst, ctx: FramelessCtx<'_, '_, '_, Arch>) -> bool {
        (self.base_matcher)(base, ctx)
    }

    #[inline(always)]
    fn matches_as_operand(
        &self,
        val: Value,
        base: ir::Inst,
        (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
    ) -> bool {
        match def.dfg.value_to_inst(val) {
            Some(inst) => {
                ctx.able_to_merge_with(inst, base) && (self.operand_matcher)(inst, base, (def, ctx))
            }
            None => false,
        }
    }

    #[inline(always)]
    fn mark_as_merged_base(&self, base: ir::Inst, ctx: FramelessCtx<'_, '_, '_, Arch>) {
        (self.base_merger)(base, ctx)
    }

    #[inline(always)]
    fn mark_as_merged_operand(
        &self,
        val: Value,
        base: ir::Inst,
        (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
    ) {
        let inst = def
            .dfg
            .value_to_inst(val)
            .expect("Self::matches_as_operand must be true before calling this");

        (self.operand_merger)(inst, base, (def, ctx))
    }
}

struct ISelMergeAnyMatcher<Arch: Architecture> {
    _unused: PhantomData<fn() -> Arch>,
}

impl<Arch: Architecture> Clone for ISelMergeAnyMatcher<Arch> {
    fn clone(&self) -> Self {
        Self {
            _unused: PhantomData,
        }
    }
}

impl<Arch> Copy for ISelMergeAnyMatcher<Arch> where Arch: Architecture {}

impl<Arch: Architecture> ISelMergeMatcher<Arch> for ISelMergeAnyMatcher<Arch> {
    #[inline(always)]
    fn matches_as_base(&self, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) -> bool {
        true
    }

    #[inline(always)]
    fn matches_as_operand(&self, _: Value, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) -> bool {
        true
    }

    #[inline(always)]
    fn mark_as_merged_base(&self, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) {
        /* nothing to merge, this is explicitly the "any value in a register" case */
    }

    #[inline(always)]
    fn mark_as_merged_operand(&self, _: Value, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) {
        /* nothing to merge, this is explicitly the "any value in a register" case */
    }
}

struct ISelMergePhiMatcher<Arch: Architecture> {
    _unused: PhantomData<fn() -> Arch>,
}

impl<Arch: Architecture> Clone for ISelMergePhiMatcher<Arch> {
    fn clone(&self) -> Self {
        Self {
            _unused: PhantomData,
        }
    }
}

impl<Arch> Copy for ISelMergePhiMatcher<Arch> where Arch: Architecture {}

impl<Arch: Architecture> ISelMergeMatcher<Arch> for ISelMergePhiMatcher<Arch> {
    #[inline(always)]
    fn matches_as_base(&self, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) -> bool {
        // phis are never instructions
        false
    }

    #[inline(always)]
    fn matches_as_operand(
        &self,
        value: Value,
        _: ir::Inst,
        (def, _): FramelessCtx<'_, '_, '_, Arch>,
    ) -> bool {
        def.dfg.is_block_param(value)
    }

    #[inline(always)]
    fn mark_as_merged_base(&self, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) {
        /* nothing to merge, this is explicitly the "phi (which is in a register)" case */
    }

    #[inline(always)]
    fn mark_as_merged_operand(&self, _: Value, _: ir::Inst, _: FramelessCtx<'_, '_, '_, Arch>) {
        /* nothing to merge, this is explicitly the "phi (which is in a register)" case */
    }
}

/// Matches any instruction, or anything else that produces a value.
///
/// This is effectively the "stop matching" marker when making a pattern,
/// e.g. the pattern `iadd(any(), iconst(5))` would match the following IR:
///
/// ```text
/// bb0(i32 %0):
///   %1 = iconst i32 5
///   %2 = iadd i32 %0, %1
/// ```
///
/// `any()` will match the phi node, but it would have also matched anything else.
#[inline(always)]
pub fn any<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    ISelMergeAnyMatcher {
        _unused: PhantomData,
    }
}

/// Matches any block parameter (aka phi nodes).
///
/// This is a more specific "stop matching" marker when making a pattern,
/// e.g. the pattern `iadd(phi(), iconst(5))` would match the following IR:
///
/// ```text
/// bb0(i32 %0):
///   %1 = iconst i32 5
///   %2 = iadd i32 %0, %1
/// ```
///
/// but would not match this IR:
///
/// ```text
/// bb0:
///   %1 = iconst i32 5
///   %2 = iadd i32 %1, %1
/// ```
#[inline(always)]
pub fn phi<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    ISelMergePhiMatcher {
        _unused: PhantomData,
    }
}

/// Matches any `load` instruction.
#[inline(always)]
pub fn load<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    BasicISelMergeMatcher {
        base_matcher: |base, (def, _)| matches!(def.dfg.inst_data(base), InstData::Load(_)),
        operand_matcher: |inst, _, (def, _)| matches!(def.dfg.inst_data(inst), InstData::Load(_)),
        base_merger: |_, (_, _)| { /* nothing matched, nothing merged */ },
        operand_merger: |inst, base, (_, ctx)| {
            ctx.mark_merged_with(inst, base);
        },
        _unused: PhantomData,
    }
}

/// Matches any `iconst` instruction.
#[inline(always)]
pub fn iconst<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    BasicISelMergeMatcher {
        base_matcher: |base, (def, _)| matches!(def.dfg.inst_data(base), InstData::IConst(_)),
        operand_matcher: |inst, _, (def, _)| matches!(def.dfg.inst_data(inst), InstData::IConst(_)),
        base_merger: |_, (_, _)| { /* nothing matched, nothing merged */ },
        operand_merger: |inst, base, (_, ctx)| {
            ctx.mark_merged_with(inst, base);
        },
        _unused: PhantomData,
    }
}

/// Matches any `iconst` instruction with any value.
#[inline(always)]
pub fn iconst_val<Arch: Architecture>(val: u64) -> impl ISelMergeMatcher<Arch> + Copy {
    BasicISelMergeMatcher {
        base_matcher: move |base, (def, _)| match def.dfg.inst_data(base) {
            InstData::IConst(iconst) => iconst.value() == val,
            _ => false,
        },
        operand_matcher: move |inst, _, (def, _)| match def.dfg.inst_data(inst) {
            InstData::IConst(iconst) => iconst.value() == val,
            _ => false,
        },
        base_merger: |_, (_, _)| { /* nothing matched, nothing merged */ },
        operand_merger: |inst, base, (_, ctx)| {
            ctx.mark_merged_with(inst, base);
        },
        _unused: PhantomData,
    }
}

/// Matches any `iconst` instruction that has a value that can fit in an imm32
#[inline(always)]
pub fn imm32<'a, Arch: Architecture + 'a>(
    val: &'a RefCell<i32>,
) -> impl ISelMergeMatcher<Arch> + Copy + 'a {
    #[inline(always)]
    fn match_if(inst: ir::Inst, val: &RefCell<i32>, def: &FunctionDefinition) -> bool {
        match def.dfg.inst_data(inst) {
            InstData::IConst(iconst) => {
                let (fits, as_u32) = match iconst.result_ty().unwrap().as_int().unwrap().width() {
                    8 | 16 | 32 => (true, iconst.value() as u32),
                    64 => {
                        let result = i32::try_from(iconst.value() as i64);

                        match result {
                            Ok(val) => (true, val as u32),
                            Err(e) => (false, 0),
                        }
                    }
                    _ => unreachable!(),
                };

                if fits {
                    *val.borrow_mut() = as_u32 as i32;
                }

                fits
            }
            InstData::Null(_) => {
                *val.borrow_mut() = 0;

                true
            }
            _ => false,
        }
    }

    BasicISelMergeMatcher {
        base_matcher: move |base, (def, _)| match_if(base, val, def),
        operand_matcher: move |inst, _, (def, _)| match_if(inst, val, def),
        base_merger: |_, (_, _)| { /* nothing matched, nothing merged */ },
        operand_merger: |inst, base, (_, ctx)| {
            ctx.mark_merged_with(inst, base);
        },
        _unused: PhantomData,
    }
}

macro_rules! parameterless_match_if_pattern {
    ($match_if:expr) => {
        BasicISelMergeMatcher {
            base_matcher: move |base, (def, _)| $match_if(base, def),
            operand_matcher: move |inst, _, (def, _)| $match_if(inst, def),
            base_merger: |_, (_, _)| { /* nothing matched, nothing merged */ },
            operand_merger: |inst, base, (_, ctx)| {
                ctx.mark_merged_with(inst, base);
            },
            _unused: PhantomData::default(),
        }
    };
}

/// Matches any instruction that yields a constant `0` value
#[inline(always)]
pub fn zero<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    #[inline(always)]
    fn match_if(inst: ir::Inst, def: &FunctionDefinition) -> bool {
        match def.dfg.inst_data(inst) {
            InstData::IConst(iconst) => iconst.value() == 0,
            InstData::Null(_) => true,
            _ => false,
        }
    }

    parameterless_match_if_pattern!(match_if)
}

/// Matches an integral constant of `-1` for any integer type
#[inline(always)]
pub fn neg1<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    #[inline(always)]
    fn match_if(inst: ir::Inst, def: &FunctionDefinition) -> bool {
        match def.dfg.inst_data(inst) {
            InstData::IConst(iconst) => iconst.value() == (u64::MAX & iconst.mask()),
            _ => false,
        }
    }

    parameterless_match_if_pattern!(match_if)
}

/// Matches on an `iconst` instruction, and sets `val` to the value the `iconst` produces.
///
/// This is used for times when only specific values can be merged, e.g. immediates that need
/// to fit inside an `i32`.
#[inline(always)]
pub fn iconst_of<'a, Arch: Architecture + 'a>(
    val: &'a RefCell<u64>,
) -> impl ISelMergeMatcher<Arch> + Copy + 'a {
    BasicISelMergeMatcher {
        base_matcher: move |base, (def, _)| match def.dfg.inst_data(base) {
            InstData::IConst(iconst) => {
                *val.borrow_mut() = iconst.value();

                true
            }
            _ => false,
        },
        operand_matcher: move |inst, _, (def, _)| match def.dfg.inst_data(inst) {
            InstData::IConst(iconst) => {
                *val.borrow_mut() = iconst.value();

                true
            }
            _ => false,
        },
        base_merger: |_, (_, _)| { /* nothing matched, nothing merged */ },
        operand_merger: |inst, base, (_, ctx)| {
            ctx.mark_merged_with(inst, base);
        },
        _unused: PhantomData,
    }
}

macro_rules! binary_pattern {
    ($name:ident, $variant:path, $underlying:ty, $str:literal) => {
        paste! {
            #[doc = concat!("Matches against `", $str, "` instructions, ignoring operands")]
            #[inline(always)]
            pub fn [< $name >]<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
                BasicISelMergeMatcher {
                    base_matcher: |base, (def, _)| matches!(def.dfg.inst_data(base), InstData::$variant(_)),
                    operand_matcher: |inst, _, (def, _)| matches!(def.dfg.inst_data(inst), InstData::$variant(_)),
                    base_merger: |_, (_, _)| { /* no operands matched, nothing merged */ },
                    operand_merger: |inst, base, (_, ctx)| {
                        ctx.mark_merged_with(inst, base);
                    },
                    _unused: PhantomData::default(),
                }
            }

            #[doc = concat!("Matching against `", $str, "` instructions and their operands")]
            pub fn [< $name _with >]<A, B, Arch>(
                lhs: A,
                rhs: B,
            ) -> impl ISelMergeMatcher<Arch> + Copy
            where
                Arch: Architecture,
                A: ISelMergeMatcher<Arch> + Copy,
                B: ISelMergeMatcher<Arch> + Copy,
            {
                #[inline(always)]
                fn match_if<A, B, Arch>(
                    inst: ir::Inst,
                    base: ir::Inst,
                    lhs: A,
                    rhs: B,
                    (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
                ) -> bool
                where
                    Arch: Architecture,
                    A: ISelMergeMatcher<Arch> + Copy,
                    B: ISelMergeMatcher<Arch> + Copy,
                {
                    if let InstData::$variant(p) = def.dfg.inst_data(inst) {
                        lhs.matches_as_operand(p.lhs(), base, (def, ctx))
                            && rhs.matches_as_operand(p.rhs(), base, (def, ctx))
                    } else {
                        false
                    }
                }

                #[inline(always)]
                fn merge<A, B, Arch>(
                    inst: ir::Inst,
                    base: ir::Inst,
                    lhs: A,
                    rhs: B,
                    (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
                ) where
                    Arch: Architecture,
                    A: ISelMergeMatcher<Arch> + Copy,
                    B: ISelMergeMatcher<Arch> + Copy,
                {
                    if let InstData::$variant(p) = def.dfg.inst_data(inst) {
                        lhs.mark_as_merged_operand(p.lhs(), base, (def, ctx));
                        rhs.mark_as_merged_operand(p.rhs(), base, (def, ctx));
                    } else {
                        unreachable!()
                    }
                }

                BasicISelMergeMatcher {
                    base_matcher: move |base, (def, ctx)| {
                        // we can use base as the inst too, doesn't affect the result
                        match_if(base, base, lhs, rhs, (def, ctx))
                    },
                    operand_matcher: move |inst, base, (def, ctx)| {
                        match_if(inst, base, lhs, rhs, (def, ctx))
                    },
                    base_merger: move |base, (def, ctx)| {
                        // don't need to mark base as merged, just need to merge children
                        merge(base, base, lhs, rhs, (def, ctx));
                    },
                    operand_merger: move |inst, base, (def, ctx)| {
                        ctx.mark_merged_with(inst, base);
                        merge(inst, base, lhs, rhs, (def, ctx));
                    },
                    _unused: PhantomData::default(),
                }
            }
        }
    }
}

binary_pattern!(and, And, CommutativeArithInst, "and");
binary_pattern!(or, Or, CommutativeArithInst, "or");
binary_pattern!(xor, Xor, CommutativeArithInst, "xor");
binary_pattern!(shl, Shl, ArithInst, "shl");
binary_pattern!(ashr, AShr, ArithInst, "ashr");
binary_pattern!(lshr, LShr, ArithInst, "lshr");
binary_pattern!(iadd, IAdd, CommutativeArithInst, "iadd");
binary_pattern!(isub, ISub, ArithInst, "isub");
binary_pattern!(imul, IMul, CommutativeArithInst, "imul");
binary_pattern!(sdiv, SDiv, ArithInst, "sdiv");
binary_pattern!(udiv, UDiv, ArithInst, "udiv");
binary_pattern!(srem, SRem, ArithInst, "srem");
binary_pattern!(urem, URem, ArithInst, "urem");
binary_pattern!(fadd, FAdd, CommutativeArithInst, "fadd");
binary_pattern!(fsub, FSub, ArithInst, "fsub");
binary_pattern!(fmul, FMul, CommutativeArithInst, "fmul");
binary_pattern!(fdiv, FDiv, ArithInst, "fdiv");
binary_pattern!(frem, FRem, ArithInst, "frem");

/// Matches on any `icmp` instruction without matching on any of its operands.
#[inline(always)]
pub fn icmp<Arch: Architecture>() -> impl ISelMergeMatcher<Arch> + Copy {
    BasicISelMergeMatcher {
        base_matcher: |base, (def, _)| matches!(def.dfg.inst_data(base), InstData::ICmp(_)),
        operand_matcher: |inst, _, (def, _)| matches!(def.dfg.inst_data(inst), InstData::ICmp(_)),
        base_merger: |_, (_, _)| { /* no operands matched, nothing merged */ },
        operand_merger: |inst, base, (_, ctx)| {
            ctx.mark_merged_with(inst, base);
        },
        _unused: PhantomData,
    }
}

/// Matches on an `icmp` instruction with a specific condition, and two matching operands.
#[inline(always)]
pub fn icmp_with<A, B, Arch>(op: ICmpOp, lhs: A, rhs: B) -> impl ISelMergeMatcher<Arch> + Copy
where
    Arch: Architecture,
    A: ISelMergeMatcher<Arch> + Copy,
    B: ISelMergeMatcher<Arch> + Copy,
{
    #[inline(always)]
    fn match_if<A, B, Arch>(
        inst: ir::Inst,
        base: ir::Inst,
        op: ICmpOp,
        lhs: A,
        rhs: B,
        (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
    ) -> bool
    where
        Arch: Architecture,
        A: ISelMergeMatcher<Arch> + Copy,
        B: ISelMergeMatcher<Arch> + Copy,
    {
        if let InstData::ICmp(icmp) = def.dfg.inst_data(inst) {
            icmp.op() == op
                && lhs.matches_as_operand(icmp.lhs(), base, (def, ctx))
                && rhs.matches_as_operand(icmp.rhs(), base, (def, ctx))
        } else {
            false
        }
    }

    #[inline(always)]
    fn merge<A, B, Arch>(
        inst: ir::Inst,
        base: ir::Inst,
        lhs: A,
        rhs: B,
        (def, ctx): FramelessCtx<'_, '_, '_, Arch>,
    ) where
        Arch: Architecture,
        A: ISelMergeMatcher<Arch> + Copy + Clone,
        B: ISelMergeMatcher<Arch> + Copy + Clone,
    {
        if let InstData::ICmp(icmp) = def.dfg.inst_data(inst) {
            lhs.mark_as_merged_operand(icmp.lhs(), base, (def, ctx));
            rhs.mark_as_merged_operand(icmp.rhs(), base, (def, ctx));
        } else {
            unreachable!()
        }
    }

    BasicISelMergeMatcher {
        base_matcher: move |base, (def, ctx)| {
            // we can use base as the inst too, doesn't affect the result
            match_if(base, base, op, lhs, rhs, (def, ctx))
        },
        operand_matcher: move |inst, base, (def, ctx)| {
            match_if(inst, base, op, lhs, rhs, (def, ctx))
        },
        base_merger: move |base, (def, ctx)| {
            // don't need to mark base as merged, just need to merge children
            merge(base, base, lhs, rhs, (def, ctx));
        },
        operand_merger: move |inst, base, (def, ctx)| {
            ctx.mark_merged_with(inst, base);
            merge(inst, base, lhs, rhs, (def, ctx));
        },
        _unused: PhantomData,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::x86_64::*;
    use crate::ir::*;

    #[test]
    fn works() {
        // this is all setup, skip to the {}s
        let mut module = Module::new("main");
        let mut b = module.define_function(
            "main",
            SigBuilder::new()
                .params(&[Type::i32(), Type::ptr()])
                .ret(Some(Type::i32()))
                .build(),
        );

        let bb0 = b.create_block("bb0");
        let params = b.append_entry_params(bb0, DebugInfo::fake());
        let v0 = params[0];

        b.switch_to(bb0);
        let v2 = b.append().iconst(Type::i32(), 0, DebugInfo::fake());
        let v3 = b.append().icmp_eq(v0, v2, DebugInfo::fake());
        b.append().ret_val(v3, DebugInfo::fake());
        let main = b.define();

        let options = CodegenOptions::default();
        let mut target = PresetTargets::linux_x86_64(options);

        let function = module.function(main);
        let def = function.definition().unwrap();
        let v2inst = def.dfg.value_to_inst(v2).unwrap();
        let v3inst = def.dfg.value_to_inst(v3).unwrap();

        // two-step base
        {
            let mut ctx = LoweringContext::<X86_64>::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = icmp_with(ICmpOp::EQ, any(), iconst());

            assert!(matches(v3inst, (def, &mut ctx), &matcher));

            mark_merged(v3inst, (def, &mut ctx), &matcher);

            assert!(ctx.is_merged(v2inst));
        }

        // single-step base
        {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = icmp_with(ICmpOp::EQ, any(), iconst());

            assert!(merge_if_matches(v3inst, (def, &mut ctx), matcher));
            assert!(ctx.is_merged(v2inst));
        }

        // two-step operand
        {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = iconst();

            assert!(matches_operand(v2, v3inst, (def, &mut ctx), &matcher));

            mark_merged_operand(v2, v3inst, (def, &mut ctx), &matcher);

            assert!(ctx.is_merged(v2inst));
        }

        // one-step operand
        {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = iconst();

            assert!(merge_if_matches_operand(
                v2,
                v3inst,
                (def, &mut ctx),
                matcher
            ));
            assert!(ctx.is_merged(v2inst));
        }
    }

    #[test]
    fn binary_patterns() {
        let mut module = Module::new("main");
        let mut b = module.define_function(
            "test",
            SigBuilder::new()
                .params(&[Type::i32(), Type::ptr()])
                .ret(Some(Type::i32()))
                .build(),
        );

        let bb0 = b.create_block("bb0");
        let params = b.append_entry_params(bb0, DebugInfo::fake());
        let v0 = params[0];

        b.switch_to(bb0);
        let v2 = b.append().iconst(Type::i32(), 13, DebugInfo::fake());
        let v3 = b.append().iadd(v0, v2, DebugInfo::fake());
        b.append().ret_val(v3, DebugInfo::fake());
        let main = b.define();

        let options = CodegenOptions::default();
        let mut target = PresetTargets::linux_x86_64(options);

        let function = module.function(main);
        let def = function.definition().unwrap();
        let v2inst = def.dfg.value_to_inst(v2).unwrap();
        let v3inst = def.dfg.value_to_inst(v3).unwrap();

        let mut ctx = LoweringContext::new_for(&mut target, &module);
        ctx.prepare_for_func(function);

        let matcher = iadd_with(any(), iconst_val(13));

        assert!(merge_if_matches(v3inst, (def, &mut ctx), matcher));
        assert!(ctx.is_merged(v2inst));
    }

    #[test]
    fn imm32() {
        let mut module = Module::new("main");
        let foo_sig = SigBuilder::new()
            .params(&[
                Type::i64(),
                Type::i64(),
                Type::i64(),
                Type::i64(),
                Type::i64(),
                Type::i64(),
                Type::i64(),
            ])
            .build();
        let foo = module.declare_function("foo", foo_sig.clone());
        let mut b = module.define_function("imm32", SigBuilder::new().build());

        let foo_sig_ref = b.import_signature(&foo_sig);
        let bb0 = b.create_block("bb0");

        b.switch_to(bb0);
        let v0_yes = b.append().iconst(Type::i64(), 0, DebugInfo::fake());
        let v1_yes = b
            .append()
            .iconst(Type::i64(), (-1_i64) as u64, DebugInfo::fake());
        let v2_yes = b
            .append()
            .iconst(Type::i64(), i32::MIN as u64, DebugInfo::fake());
        let v3_yes = b
            .append()
            .iconst(Type::i64(), i32::MAX as u64, DebugInfo::fake());
        let v4_yes = b.append().iconst(Type::i64(), 5, DebugInfo::fake());
        let v5_no = b.append().iconst(
            Type::i64(),
            ((i32::MIN as i64) - 1) as u64,
            DebugInfo::fake(),
        );
        let v6_no = b
            .append()
            .iconst(Type::i64(), (i32::MAX as u64) + 1, DebugInfo::fake());

        // they need to be used for these matchers to work
        let uses_all = b.append().call(
            foo,
            foo_sig_ref,
            &[v0_yes, v1_yes, v2_yes, v3_yes, v4_yes, v5_no, v6_no],
            DebugInfo::fake(),
        );
        b.append().ret_void(DebugInfo::fake());
        let main = b.define();

        let options = CodegenOptions::default();
        let mut target = PresetTargets::linux_x86_64(options);

        let function = module.function(main);
        let def = function.definition().unwrap();

        for val in [v0_yes, v1_yes, v2_yes, v3_yes, v4_yes] {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let refcell = RefCell::new(0);
            let matcher = super::imm32(&refcell);

            assert!(matches_operand(val, uses_all, (def, &mut ctx), &matcher));
        }

        for val in [v5_no, v6_no] {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let refcell = RefCell::new(0);
            let matcher = super::imm32(&refcell);

            assert!(!matches_operand(val, uses_all, (def, &mut ctx), &matcher));
        }
    }

    #[test]
    fn zero() {
        let mut module = Module::new("main");
        let foo_sig = SigBuilder::new()
            .params(&[
                Type::i8(),
                Type::i16(),
                Type::i32(),
                Type::i64(),
                Type::i32(),
                Type::i32(),
            ])
            .build();
        let foo = module.declare_function("foo", foo_sig.clone());
        let mut b = module.define_function("imm32", SigBuilder::new().build());

        let foo_sig_ref = b.import_signature(&foo_sig);
        let bb0 = b.create_block("bb0");

        b.switch_to(bb0);
        let v0 = b.append().iconst(Type::i8(), 0, DebugInfo::fake());
        let v1 = b.append().iconst(Type::i16(), 0, DebugInfo::fake());
        let v2 = b.append().iconst(Type::i32(), 0, DebugInfo::fake());
        let v3 = b.append().iconst(Type::i64(), 0, DebugInfo::fake());
        let v4 = b.append().null(Type::i32(), DebugInfo::fake());
        let v5_not = b.append().iconst(Type::i32(), 1, DebugInfo::fake());

        // they need to be used for these matchers to work
        let uses_all = b.append().call(
            foo,
            foo_sig_ref,
            &[v0, v1, v2, v3, v4, v5_not],
            DebugInfo::fake(),
        );
        b.append().ret_void(DebugInfo::fake());
        let main = b.define();

        let options = CodegenOptions::default();
        let mut target = PresetTargets::linux_x86_64(options);

        let function = module.function(main);
        let def = function.definition().unwrap();

        for val in [v0, v1, v2, v3, v4] {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = super::zero();

            assert!(matches_operand(val, uses_all, (def, &mut ctx), &matcher));
        }

        {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = super::zero();

            assert!(!matches_operand(
                v5_not,
                uses_all,
                (def, &mut ctx),
                &matcher
            ));
        }
    }

    #[test]
    fn neg1() {
        let mut module = Module::new("main");
        let foo_sig = SigBuilder::new()
            .params(&[
                Type::i8(),
                Type::i16(),
                Type::i32(),
                Type::i64(),
                Type::i32(),
                Type::i64(),
                Type::i64(),
            ])
            .build();
        let foo = module.declare_function("foo", foo_sig.clone());
        let mut b = module.define_function("imm32", SigBuilder::new().build());

        let foo_sig_ref = b.import_signature(&foo_sig);
        let bb0 = b.create_block("bb0");

        b.switch_to(bb0);
        let v0 = b
            .append()
            .iconst(Type::i8(), (-1_i64) as u64, DebugInfo::fake());
        let v1 = b
            .append()
            .iconst(Type::i16(), (-1_i64) as u64, DebugInfo::fake());
        let v2 = b
            .append()
            .iconst(Type::i32(), (-1_i64) as u64, DebugInfo::fake());
        let v3 = b
            .append()
            .iconst(Type::i64(), (-1_i64) as u64, DebugInfo::fake());
        let v4_not = b
            .append()
            .iconst(Type::i32(), (-2_i64) as u64, DebugInfo::fake());
        let v5_not = b
            .append()
            .iconst(Type::i64(), (-2_i64) as u64, DebugInfo::fake());
        let v6_not = b.append().iconst(Type::i64(), 1, DebugInfo::fake());

        // they need to be used for these matchers to work
        let uses_all = b.append().call(
            foo,
            foo_sig_ref,
            &[v0, v1, v2, v3, v4_not, v5_not, v6_not],
            DebugInfo::fake(),
        );
        b.append().ret_void(DebugInfo::fake());
        let main = b.define();

        let options = CodegenOptions::default();
        let mut target = PresetTargets::linux_x86_64(options);

        let function = module.function(main);
        let def = function.definition().unwrap();

        for val in [v0, v1, v2, v3] {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = super::neg1();

            assert!(matches_operand(val, uses_all, (def, &mut ctx), &matcher));
        }

        for val in [v4_not, v5_not, v6_not] {
            let mut ctx = LoweringContext::new_for(&mut target, &module);
            ctx.prepare_for_func(function);

            let matcher = super::neg1();

            assert!(!matches_operand(val, uses_all, (def, &mut ctx), &matcher));
        }
    }
}
