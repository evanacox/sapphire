//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Defines APIs for pattern-matching on SIR.
//!
//! This is meant for use at the SIR level, instruction selection needs
//! different matchers due to extra invariants needing to be checked.
//!
//! ```
//! # use sapphire::ir::matchers::*;
//! # use sapphire::ir::*;
//! let mut module = Module::new("test");
//! let mut b = module.define_function("test", SigBuilder::new().ret(Some(Type::i32())).build());
//! let bb0 = b.create_block("bb0");
//! b.switch_to(bb0);
//!
//! let v1 = b.append().iconst(Type::i32(), 42, DebugInfo::fake());
//! let v2 = b.append().iconst(Type::i32(), 16, DebugInfo::fake());
//! let v3 = b.append().iadd(v2, v1, DebugInfo::fake());
//! let v4 = b.append().imul(v1, v3, DebugInfo::fake());
//! b.append().ret_val(v4, DebugInfo::fake());
//!
//! let f = b.define();
//! let dfg = &module.function(f).definition().unwrap().dfg;
//!
//! let iconst_42 = iconst_val(42);
//! let iconst_i32 = iconst_ty(Type::i32());
//! let iadd_i32_42 = iadd_with(val_of_ty(Type::i32()), iconst_ty_val(Type::i32(), 42));
//!
//! assert!(matches(v1, iconst_42, dfg));
//! assert!(matches(v3, iadd_i32_42, dfg));
//! ```

use crate::ir::*;
use paste::paste;
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

/// Returns whether or not a value matches the provided matcher
pub fn matches<'a>(val: Value, matcher: impl IRMatcher<'a>, dfg: &'a DataFlowGraph) -> bool {
    matcher.matches_val(val, dfg)
}

/// Returns whether or not an instruction matches the provided matcher
pub fn matches_inst<'a>(inst: Inst, matcher: impl IRMatcher<'a>, dfg: &'a DataFlowGraph) -> bool {
    matcher.matches_inst(inst, dfg)
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

/// A matcher that matches on values
pub struct BasicValMatcher<'a, F>
where
    F: FnOnce(Value, &'a DataFlowGraph) -> bool + 'a,
{
    matcher: F,
    data: PhantomData<&'a i32>,
}

impl<'a, F> IRMatcher<'a> for BasicValMatcher<'a, F>
where
    F: FnOnce(Value, &'a DataFlowGraph) -> bool,
{
    fn matches_inst(self, inst: Inst, dfg: &'a DataFlowGraph) -> bool {
        match dfg.inst_to_result(inst) {
            Some(val) => self.matches_val(val, dfg),
            None => false,
        }
    }

    fn matches_val(self, val: Value, dfg: &'a DataFlowGraph) -> bool {
        (self.matcher)(val, dfg)
    }
}

/// Logical conjunction operation between two matchers.
///
/// The IR being matched must match both matchers provided, or this
/// matcher doesn't match.
pub fn both<'a, 'b, 'c, B, C>(lhs: B, rhs: C) -> impl IRMatcher<'a>
where
    'a: 'b,
    'a: 'c,
    B: IRMatcher<'b> + 'a,
    C: IRMatcher<'c> + 'a,
{
    BasicInstMatcher {
        matcher: |inst, dfg| lhs.matches_inst(inst, dfg) && rhs.matches_inst(inst, dfg),
        data: PhantomData::default(),
    }
}

/// Logical disjunction operation between two matchers.
///
/// The IR being matched must match one of the matchers provided, or this
/// matcher doesn't match.
pub fn one_of<'a, 'b, 'c, B, C>(lhs: B, rhs: C) -> impl IRMatcher<'a>
where
    'a: 'b,
    'a: 'c,
    B: IRMatcher<'b> + 'a,
    C: IRMatcher<'c> + 'a,
{
    BasicInstMatcher {
        matcher: |inst, dfg| lhs.matches_inst(inst, dfg) || rhs.matches_inst(inst, dfg),
        data: PhantomData::default(),
    }
}

/// A matcher that matches any value
pub fn val<'a>() -> impl IRMatcher<'a> {
    BasicValMatcher {
        matcher: move |_, _| true,
        data: PhantomData::default(),
    }
}

/// A matcher that matches any value with a given type
pub fn val_of_ty<'a>(ty: Type) -> impl IRMatcher<'a> {
    BasicValMatcher {
        matcher: move |val, dfg| dfg.ty(val) == ty,
        data: PhantomData::default(),
    }
}

/// A matcher that matches any value coming from a φ node.
pub fn block_param<'a>() -> impl IRMatcher<'a> {
    BasicValMatcher {
        matcher: move |val, dfg| dfg.is_block_param(val),
        data: PhantomData::default(),
    }
}

/// A matcher that matches any value coming from a φ node that also has a given type.
pub fn block_param_of_ty<'a>(ty: Type) -> impl IRMatcher<'a> {
    BasicValMatcher {
        matcher: move |val, dfg| dfg.is_block_param(val) && dfg.ty(val) == ty,
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `iconst` instructions (i.e. matches on constant operands).
pub fn iconst<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::IConst(_)),
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `iconst` instructions with a specific value
pub fn iconst_val<'a>(value: u64) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::IConst(iconst) => iconst.value() == value,
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `iconst` instructions with a specific type
pub fn iconst_ty<'a>(ty: Type) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::IConst(iconst) => iconst.result_ty().unwrap() == ty,
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `iconst` instructions with a specific value *and*
/// a specific type.
pub fn iconst_ty_val<'a>(ty: Type, value: u64) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::IConst(iconst) => {
                iconst.value() == value && iconst.result_ty().unwrap() == ty
            }
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// Matches on an `iconst` value that is a power of 2
pub fn power_of_two<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::IConst(iconst) => iconst.value().is_power_of_two(),
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `fconst` instructions (i.e. matches on constant operands).
pub fn fconst<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::FConst(_)),
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `fconst` instructions with a specific type
pub fn fconst_ty<'a>(ty: Type) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::FConst(fconst) => fconst.result_ty().unwrap() == ty,
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `null` instructions (i.e. matches on constant operands).
pub fn null<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::Null(_)),
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `null` instructions with a specific type
pub fn null_ty<'a>(ty: Type) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::Null(null) => null.result_ty().unwrap() == ty,
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `null` instructions with an integer type
pub fn null_int<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::Null(null) => null.result_ty().unwrap().is_int(),
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `null` instructions with an integer, boolean or pointer type
pub fn null_integral<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::Null(null) => {
                let ty = null.result_ty().unwrap();

                ty.is_bool_or_int() || ty.is_ptr()
            }
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `null` instructions with a floating-point type
pub fn null_float<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::Null(null) => null.result_ty().unwrap().is_float(),
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `undef` instructions (i.e. matches on constant operands).
pub fn undef<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::Undef(_)),
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `bconst` instructions (i.e. matches on constant operands).
pub fn bconst<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::BConst(_)),
        data: PhantomData::default(),
    }
}

/// A matcher that matches on `bconst` instructions with a specific value
pub fn bconst_val<'a>(value: bool) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| match dfg.inst_data(inst) {
            InstData::BConst(bconst) => bconst.value() == value,
            _ => false,
        },
        data: PhantomData::default(),
    }
}

/// Matches a `stackslot` instruction
pub fn stackslot<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::StackSlot(_)),
        data: PhantomData::default(),
    }
}

/// Matches a `load` instruction
pub fn load<'a>() -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::Load(_)),
        data: PhantomData::default(),
    }
}

macro_rules! binary_matcher {
    ($name:ident, $variant:path, $underlying:ty, $str:literal) => {
        paste! {
            #[doc = concat!("Allows matching against `", $str, "` instructions.")]
            #[doc = ""]
            #[doc = concat!("If an instruction has the `", $str, "` opcode (or a value is the result of an")]
            #[doc = "instruction with that opcode), this will match."]
            pub fn [< $name >]<'a>() -> impl IRMatcher<'a> {
                BasicInstMatcher {
                    matcher: move |inst, dfg| matches!(dfg.inst_data(inst), InstData::$variant(_)),
                    data: PhantomData::default(),
                }
            }

            #[doc = concat!("Allows matching against `", $str, "` instructions and their lhs/rhs.")]
            #[doc = ""]
            #[doc = "Runs matchers on the left-hand side and the right-hand side operands. If the opcode and both the"]
            #[doc = "left-hand side and right-hand side matches, this will match."]
            pub fn [< $name _with >]<'a, 'b, 'c, B, C>(
                lhs: B,
                rhs: C
            ) -> impl IRMatcher<'a>
            where
                'a: 'b,
                'a: 'c,
                B: IRMatcher<'b> + 'a,
                C: IRMatcher<'c> + 'a
            {
                BasicInstMatcher {
                    matcher: |inst, dfg| {
                        match dfg.inst_data(inst) {
                            InstData::$variant(inst) => {
                                lhs.matches_val(inst.lhs(), dfg) && rhs.matches_val(inst.rhs(), dfg)
                            }
                            _ => false,
                        }
                    },
                    data: PhantomData::default(),
                }
            }
        }
    };
}

binary_matcher!(and, And, CommutativeArithInst, "and");
binary_matcher!(or, Or, CommutativeArithInst, "or");
binary_matcher!(xor, Xor, CommutativeArithInst, "xor");
binary_matcher!(shl, Shl, ArithInst, "shl");
binary_matcher!(ashr, AShr, ArithInst, "ashr");
binary_matcher!(lshr, LShr, ArithInst, "lshr");
binary_matcher!(icmp, ICmp, ICmpInst, "icmp");
binary_matcher!(fcmp, FCmp, FCmpInst, "fcmp");
binary_matcher!(iadd, IAdd, CommutativeArithInst, "iadd");
binary_matcher!(isub, ISub, ArithInst, "isub");
binary_matcher!(imul, IMul, CommutativeArithInst, "imul");
binary_matcher!(sdiv, SDiv, ArithInst, "sdiv");
binary_matcher!(udiv, UDiv, ArithInst, "udiv");
binary_matcher!(srem, SRem, ArithInst, "srem");
binary_matcher!(urem, URem, ArithInst, "urem");
binary_matcher!(fadd, FAdd, CommutativeArithInst, "fadd");
binary_matcher!(fsub, FSub, ArithInst, "fsub");
binary_matcher!(fmul, FMul, CommutativeArithInst, "fmul");
binary_matcher!(fdiv, FDiv, ArithInst, "fdiv");
binary_matcher!(frem, FRem, ArithInst, "frem");

/// A matcher that matches any binary instruction.
pub fn binary<'a>(out: &'a mut Option<&'a (dyn BinaryInst + 'a)>) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: |inst, dfg| {
            *out = match dfg.inst_data(inst) {
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

macro_rules! matches_lhs_rhs {
    ($inst:expr, $dfg:expr, $lhs:expr, $rhs:expr) => {{
        let result = $lhs.matches_val($inst.lhs(), $dfg) && $rhs.matches_val($inst.rhs(), $dfg);

        result.then_some($inst)
    }};
}

/// A matcher that matches a binary instruction.
pub fn binary_with<'a>(
    out: &'a mut Option<&'a (dyn BinaryInst + 'a)>,
    lhs: impl IRMatcher<'a> + 'a,
    rhs: impl IRMatcher<'a> + 'a,
) -> impl IRMatcher<'a> {
    BasicInstMatcher {
        matcher: move |inst, dfg| {
            *out = match dfg.inst_data(inst) {
                InstData::ICmp(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::FCmp(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::And(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::Or(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::Xor(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::Shl(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::AShr(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::LShr(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::IAdd(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::ISub(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::IMul(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::SDiv(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::UDiv(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::SRem(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::URem(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::FAdd(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::FSub(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::FMul(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::FDiv(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
                InstData::FRem(inst) => matches_lhs_rhs!(inst, dfg, lhs, rhs),
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

    macro_rules! assert_matches_val {
        ($matcher:expr, $val:expr, $cursor:expr) => {
            assert!($matcher.matches_val($val, $cursor.dfg()));
        };
    }

    macro_rules! assert_not_matches_val {
        ($matcher:expr, $val:expr, $cursor:expr) => {
            assert!(!$matcher.matches_val($val, $cursor.dfg()));
        };
    }

    #[test]
    fn test_basic() {
        let mut module = Module::new("test");
        let mut b = module.define_function("test", SigBuilder::new().param(Type::i32()).build());

        let bb0 = b.create_block("bb0");
        let vx = b.append_entry_params(bb0, DebugInfo::fake())[0];
        b.switch_to(bb0);

        let v0 = b.append().iconst(Type::i32(), 42, DebugInfo::fake());
        let v1 = b.append().iconst(Type::i32(), 6, DebugInfo::fake());
        let v2 = b.append().iadd(v0, vx, DebugInfo::fake());
        let v3 = b.append().imul(v2, vx, DebugInfo::fake());

        let f = b.define();
        let func = module.function_mut(f);
        let cursor = FuncCursor::over(func);

        assert_matches_val!(val(), vx, cursor);
        assert_matches_val!(val_of_ty(Type::i32()), vx, cursor);
        assert_matches_val!(block_param(), vx, cursor);
        assert_matches_val!(block_param_of_ty(Type::i32()), vx, cursor);
        assert_matches_val!(iconst(), v0, cursor);
        assert_matches_val!(iconst_val(42), v0, cursor);
        assert_matches_val!(iconst_ty(Type::i32()), v0, cursor);
        assert_matches_val!(iconst_ty_val(Type::i32(), 42), v0, cursor);
        assert_matches_val!(iadd(), v2, cursor);
        assert_matches_val!(iadd_with(iconst(), val()), v2, cursor);
        assert_matches_val!(iadd_with(iconst(), val_of_ty(Type::i32())), v2, cursor);
        assert_matches_val!(imul(), v3, cursor);
        assert_matches_val!(imul_with(iadd(), val()), v3, cursor);

        assert_not_matches_val!(iconst_val(42), v1, cursor);
        assert_not_matches_val!(iconst_val(6), v0, cursor);
        assert_not_matches_val!(iconst(), v2, cursor);
        assert_not_matches_val!(imul(), v2, cursor);
        assert_not_matches_val!(iadd_with(iconst(), iconst()), v2, cursor);
        assert_not_matches_val!(iadd(), v3, cursor);
        assert_not_matches_val!(iconst(), vx, cursor);
        assert_not_matches_val!(block_param(), v0, cursor);
        assert_not_matches_val!(imul_with(iconst(), val()), v3, cursor);
        assert_not_matches_val!(imul_with(block_param(), val()), v3, cursor);
    }
}
