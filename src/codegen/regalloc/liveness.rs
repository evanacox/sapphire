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
use crate::codegen::{MIRBlock, MIRFunction, MachInst, Reg};
use smallvec::SmallVec;

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
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct LiveInterval((u32, u32));

impl LiveInterval {
    /// The linear index of the instruction that defines this register
    ///
    ///
    #[inline]
    pub fn first_defined_after(self) -> u32 {
        (self.0).0
    }

    /// The linear index of the instruction that last uses this register as an input
    #[inline]
    pub fn last_used_by(self) -> u32 {
        (self.0).1
    }
}

/// Models a simpler form of live-ness, live intervals.
///
/// This effectively treats the entire function as one linear block and computes
/// the intervals of this "block" that various registers are live for.
pub struct LiveIntervals {
    // all of these are [begin, end] ranges, so they do include the last instruction they're on.
    intervals: SecondaryMap<Reg, LiveInterval>,
}

impl LiveIntervals {
    /// Computes a conservative set of live intervals for each v-reg (and p-reg).
    pub fn compute<Inst: MachInst>(mir: &MIRFunction<Inst>) -> Self {
        let intervals = SecondaryMap::default();

        for (i, &inst) in mir.all_instructions().iter().enumerate() {
            //
        }

        Self { intervals }
    }

    /// Gets the live intervals for each register. These are not sorted in any way,
    /// they are effectively in a random order.
    #[inline]
    pub fn intervals(&self) -> impl Iterator<Item = (Reg, LiveInterval)> + '_ {
        self.intervals.iter().map(|(reg, int)| (reg, *int))
    }
}
