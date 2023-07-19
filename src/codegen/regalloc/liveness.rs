//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::codegen::regalloc::allocator::{defs, uses};
use crate::codegen::{MIRBlock, MIRFunction, MachInst, ProgramPoint, Reg, StackFrame};
use smallvec::SmallVec;
use std::cmp::Ordering;
use std::fmt;

/// Models the live range information necessary for the register allocators.
///
/// This computes the `DefsIn`, `DefsOut`, `LiveIn` and `LiveOut` sets
pub struct LiveRanges {
    defs_in: SecondaryMap<MIRBlock, SmallVec<[Reg; 5]>>,
    defs_out: SecondaryMap<MIRBlock, SmallVec<[Reg; 5]>>,
}

impl LiveRanges {
    /// Computes a precise set of live ranges for each v-reg (and p-reg) in `mir`
    pub fn compute<Inst: MachInst>(mir: &MIRFunction<Inst>) -> Self {
        //
        todo!()
    }
}

/// A live interval denoting the instruction a register is first defined by
/// and the instruction a register is last used by.
///
/// This is effectively an open interval `(a, b)` of program points where
/// the register is considered to be live
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct LiveInterval((u32, u32));

impl PartialOrd for LiveInterval {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let (x1, x2) = self.0;
        let (y1, y2) = other.0;

        if x1 == y1 {
            x2.partial_cmp(&y2)
        } else if x1 == u32::MAX {
            Some(Ordering::Less)
        } else {
            x1.partial_cmp(&y1)
        }
    }
}

impl Ord for LiveInterval {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl LiveInterval {
    /// Makes a live interval representing `(start, start)`.
    #[inline]
    pub fn at(start: u32) -> Self {
        Self((start, start))
    }

    /// Makes a live interval representing `(start, end)`.
    #[inline]
    pub fn between(start: u32, end: u32) -> Self {
        Self((start, end))
    }

    /// Creates an interval that doesn't have a beginning, i.e. it is defined
    /// by the caller of the function.
    #[inline]
    pub fn defined_before_func(ends_at: u32) -> Self {
        Self((u32::MAX, ends_at))
    }

    /// The linear index of the instruction that defines this register.
    ///
    /// If this returns `None`, the value is defined prior to the first instruction.
    #[inline]
    pub fn first_defined_after(self) -> Option<u32> {
        ((self.0).0 != u32::MAX).then_some((self.0).0)
    }

    /// The linear index of the instruction that last uses this register as an input
    #[inline]
    pub fn last_used_by(self) -> u32 {
        (self.0).1
    }

    /// Checks whether the interval of program points represented by `self`
    /// overlaps with the interval represented by `other`.
    #[inline]
    pub fn overlaps(self, other: Self) -> bool {
        let (x1, x2) = self.0;
        let (y1, y2) = other.0;

        // for (x1, x2) and (y1, y2) the ranges DON'T overlap
        // when one of these conditions are true
        let self_ends_before_other = x2 <= y1;
        let other_ends_before_self = x1 >= y2;

        // different cases if either one is u32::MAX, because that means they actually
        // are a closed range starting at 0 so we can assume they go first and not check
        // the second condition
        match (x1, y1) {
            // self is [0, x2) so we ignore the other condition
            (u32::MAX, _) => !self_ends_before_other,
            // other is [0, y2) so we ignore the other condition
            (_, u32::MAX) => !other_ends_before_self,
            // usual case so we check both
            _ => !(self_ends_before_other || other_ends_before_self),
        }
    }

    /// Checks if a [`ProgramPoint`] is within the live range denoted by `self`.
    #[inline]
    pub fn within(self, pp: ProgramPoint) -> bool {
        if let Some(begin) = self.first_defined_after() {
            // if begin == offset_of_next then pp points at the instruction **before** the interval
            begin < pp.offset_of_next() && pp.offset_of_next() <= self.last_used_by()
        } else {
            pp.offset_of_next() <= self.last_used_by()
        }
    }

    /// Gets the range of program points represented by the interval
    #[inline]
    pub fn program_points(self) -> impl Iterator<Item = ProgramPoint> {
        let iter = match self.first_defined_after() {
            Some(i) => (i + 1)..=self.last_used_by(),
            None => 0..=self.last_used_by(),
        };

        iter.map(|x| ProgramPoint::before(x))
    }
}

impl fmt::Display for LiveInterval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let b = self.last_used_by();

        if let Some(a) = self.first_defined_after() {
            write!(f, "({a}, {b})")
        } else {
            write!(f, "[0, {b})")
        }
    }
}

/// Models a simpler form of live-ness, live intervals.
///
/// This effectively treats the entire function as one linear block and computes
/// the intervals of this "block" that various registers are live for.
pub struct ConservativeLiveIntervals {
    intervals: SecondaryMap<Reg, LiveInterval>,
    begins_with_copy: SecondaryMap<Reg, Reg>,
}

impl ConservativeLiveIntervals {
    /// Computes a conservative set of live intervals for each v-reg (and p-reg).
    pub fn compute<Inst: MachInst>(
        mir: &MIRFunction<Inst>,
        frame: &dyn StackFrame<Inst::Arch>,
    ) -> Self {
        let mut intervals = SecondaryMap::<Reg, LiveInterval>::default();
        let mut begins_with_copy = SecondaryMap::default();
        let unavailable = frame.registers().unavailable;

        for (i, &inst) in mir.all_instructions().iter().enumerate() {
            let uses = uses!(inst, frame);
            let defs = defs!(inst, frame);

            for (reg, size) in uses {
                // ignore base/stack pointer and things with a fixed interval defining them.
                // any other uses of physical registers is a bug in the MIR
                if let Some(preg) = reg.as_preg() {
                    debug_assert!(
                        unavailable.contains(&preg)
                            || !mir.fixed_intervals().intervals_for(preg).is_empty()
                    );

                    continue;
                }

                // if we already have an interval, extend it to this instruction.
                // if we don't already have an interval, we don't screw with it
                // since it's either an undef thing or some ABI constraint
                if let Some(interval) = intervals.get_mut(reg) {
                    *interval = match interval.first_defined_after() {
                        Some(idx) => LiveInterval::between(idx, i as u32),
                        _ => unreachable!(),
                    };
                }
            }

            for (reg, size) in defs {
                if let Some(preg) = reg.as_preg() {
                    debug_assert!(
                        unavailable.contains(&preg)
                            || !mir.fixed_intervals().intervals_for(preg).is_empty()
                    );

                    continue;
                }

                // if we don't have an interval, insert it.
                if !intervals.contains(reg) {
                    if let Some(copy) = inst.as_copy() {
                        begins_with_copy.insert(reg, copy.from);
                    }

                    intervals.insert(reg, LiveInterval::at(i as u32));
                }
            }
        }

        Self {
            intervals,
            begins_with_copy,
        }
    }

    /// Gets the live intervals for each register. These are not sorted in any way,
    /// they are effectively in a random order.
    ///
    /// The values yielded are:
    /// 1. register being defined
    /// 2. the interval the register is defined for
    /// 3. the register being copied from if the register is initially defined by a copy
    pub fn intervals(&self) -> impl Iterator<Item = (Reg, LiveInterval, Option<Reg>)> + '_ {
        self.intervals.iter().map(|(reg, int)| {
            let begins_copy = self.begins_with_copy.get(reg).copied();

            (reg, *int, begins_copy)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_overlap() {
        // (0, 5) overlaps (2, 4)
        assert!(LiveInterval::between(0, 5).overlaps(LiveInterval::between(2, 4)));

        // (0, 1) overlaps (0, 1)
        assert!(LiveInterval::between(0, 1).overlaps(LiveInterval::between(0, 1)));

        // (0, 1) overlaps (0, 2)
        assert!(LiveInterval::between(0, 1).overlaps(LiveInterval::between(0, 2)));

        // (0, 2) overlaps (0, 1)
        assert!(LiveInterval::between(0, 2).overlaps(LiveInterval::between(0, 1)));

        // (0, 1) doesnt overlap (1, 2)
        assert!(!LiveInterval::between(0, 1).overlaps(LiveInterval::between(1, 2)));

        // (1, 2) doesnt overlap (0, 1)
        assert!(!LiveInterval::between(1, 2).overlaps(LiveInterval::between(0, 1)));

        // (1, 2) overlaps (0, 3)
        assert!(LiveInterval::between(1, 2).overlaps(LiveInterval::between(0, 3)));

        // (0, 3) overlaps (1, 2)
        assert!(LiveInterval::between(0, 3).overlaps(LiveInterval::between(1, 2)));

        // [0, 3) overlaps (0, 3)
        assert!(LiveInterval::defined_before_func(3).overlaps(LiveInterval::between(0, 3)));

        // [0, 3) overlaps (0, 2)
        assert!(LiveInterval::defined_before_func(3).overlaps(LiveInterval::between(0, 2)));

        // [0, 3) overlaps (1, 2)
        assert!(LiveInterval::defined_before_func(3).overlaps(LiveInterval::between(1, 2)));

        // [0, 3) overlaps (1, 3)
        assert!(LiveInterval::defined_before_func(3).overlaps(LiveInterval::between(1, 3)));

        // [0, 3) doesn't overlap (3, 4)
        assert!(!LiveInterval::defined_before_func(3).overlaps(LiveInterval::between(3, 4)));
    }
}
