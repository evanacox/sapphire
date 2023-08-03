//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{SecondaryMap, SecondarySet};
use crate::codegen::regalloc::allocator::{defs, uses};
use crate::codegen::{
    Allocation, Architecture, AvailableRegisters, ConservativeLiveIntervals, FixedIntervals,
    LiveInterval, MIRFunction, MachInst, PReg, ProgramPoint, ProgramPointsIterator, Reg,
    RegisterAllocator, RegisterMapping, SpillReload, StackFrame, VariableLocation,
};
use crate::ir::FunctionMetadata;
use crate::utility::SaHashMap;
use smallvec::{smallvec, SmallVec};
use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
struct RegLivePair {
    /* raw: u128, */
    reg: Reg,
    live: LiveInterval,
}

impl RegLivePair {
    #[inline]
    fn new(reg: Reg, live: LiveInterval) -> Self {
        /* let (reg, live): (u32, u64) = unsafe { (mem::transmute(reg), mem::transmute(live)) };

        Self {
            raw: (reg as u128) << 64 | (live as u128),
        }
        */

        Self { reg, live }
    }

    #[inline]
    fn reg(self) -> Reg {
        /* unsafe { mem::transmute((self.raw >> 64) as u32) } */
        self.reg
    }

    #[inline]
    fn live(self) -> LiveInterval {
        /* unsafe { mem::transmute(self.raw as u64) } */
        self.live
    }
}

impl PartialOrd for RegLivePair {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.live().partial_cmp(&other.live())
    }
}

impl Ord for RegLivePair {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.live().cmp(&other.live())
    }
}

/// A linear scanning based register allocator
///
/// This allocator is a balance between compile time performance and output
/// quality, it provides a balance of both.
pub struct LinearScanRegAlloc<'a> {
    active: Vec<RegLivePair>,
    intervals: BinaryHeap<Reverse<RegLivePair>>,
    fixed: &'a FixedIntervals,
    // maps a v-reg to its live-pair
    reg_to_pair: SaHashMap<Reg, RegLivePair>,
    // maps (vreg, live interval of vreg) -> preg.
    // this is only populated if vreg hasn't been spilled
    mapping: SaHashMap<RegLivePair, PReg>,
    // maps a vreg's live interval to the register it was copied from **if**
    // it began from a copy from another register (virtual or otherwise)
    started_by_copy_from: SaHashMap<RegLivePair, Reg>,
    // maps a vreg's live interval to the register it is copied to **if**
    // it ends with a copy to another register (virtual or otherwise)
    ends_by_copy_to: SaHashMap<RegLivePair, Reg>,
    // if an interval is spilled, this maps it to a list of use points
    // where it needs to be given a register
    spill_points: SaHashMap<RegLivePair, SmallVec<[u32; 4]>>,
    // where a given v-reg was spilled to, if it was spilled
    spills: SaHashMap<Reg, VariableLocation>,
    // a bitset representing the registers that are "preserved" by the function
    // and thus need to be `push`ed or whatever by the stack frame
    preserved: SecondarySet<PReg>,
    pool: RegisterPool,
}

impl<'a> LinearScanRegAlloc<'a> {
    fn new(
        fixed: &'a FixedIntervals,
        mut live: ConservativeLiveIntervals,
        metadata: FunctionMetadata,
        available: AvailableRegisters,
    ) -> Self {
        let mut intervals = BinaryHeap::default();
        let mut started_by_copy_from = SaHashMap::default();
        let mut ends_by_copy_to = SaHashMap::default();
        let mut spill_points = SaHashMap::default();
        let mut preserved = SecondarySet::default();
        let mut reg_to_pair = SaHashMap::default();

        for (reg, interval) in live.intervals() {
            let pair = RegLivePair::new(reg, interval);
            intervals.push(Reverse(pair));
            reg_to_pair.insert(reg, pair);
        }

        // we have to do this after, because we're using `take_reload_points` to avoid
        // needing to re-create the SmallVec objects
        for &Reverse(pair) in intervals.iter() {
            if let Some(reg) = live.started_by_copy(pair.reg()) {
                started_by_copy_from.insert(pair, reg);
            }

            if let Some(reg) = live.last_use_copy(pair.reg()) {
                ends_by_copy_to.insert(pair, reg);
            }

            spill_points.insert(pair, live.take_reload_points(pair.reg()));
        }

        for &reg in available.preserved {
            preserved.insert(reg);
        }

        Self {
            intervals,
            fixed,
            started_by_copy_from,
            ends_by_copy_to,
            reg_to_pair,
            spill_points,
            preserved,
            active: Vec::default(),
            mapping: SaHashMap::default(),
            spills: SaHashMap::default(),
            pool: RegisterPool::from(metadata, available),
        }
    }
}

impl<'a> LinearScanRegAlloc<'a> {
    fn lsra<Arch: Architecture>(&mut self, frame: &mut dyn StackFrame<Arch>) {
        while let Some(Reverse(interval)) = self.intervals.pop() {
            self.expire_old_intervals(interval, frame);

            // if this is true we need more registers than the target has, so we have to spill
            if self.active.len() == self.pool.max_simultaneous_live() {
                self.spill_at_interval(interval, frame);
            } else {
                // we still might spill if every available register is fixed somehow
                self.maybe_allocate(interval, frame);
            }
        }
    }

    fn push_active(&mut self, interval: RegLivePair) {
        self.active.push(interval);

        // sort in order of increasing end points, needed for ExpireOldIntervals
        self.active
            .sort_unstable_by_key(|pair| pair.live().last_used_by())
    }

    fn maybe_allocate<Arch: Architecture>(
        &mut self,
        interval: RegLivePair,
        frame: &mut dyn StackFrame<Arch>,
    ) {
        match self.register_for_interval(interval) {
            // if we did get a valid register, mark this interval as active
            // and record the register mapping for this interval
            Some(reg) => {
                self.mapping.insert(interval, reg);
                self.push_active(interval);

                // if we ended up allocating a preserved register, we need to push it
                // in the function's prologue, so we tell the frame about that
                if self.preserved.contains(reg) {
                    frame.preserved_reg_used(reg);
                }
            }
            // if we didn't get a valid register, spill the interval anyway
            // and then return. should happen very very rarely
            None => {
                self.spill_at_interval(interval, frame);
            }
        }
    }

    // main heuristic part of this linear-scan implementation, this tries to minimize
    // the amount of copies that need to remain in the output MIR.
    //
    // right now, the main heuristic is trying to make the allocator prefer
    // getting the same register as the interval that we're copying from,
    // therefore making a `x <- x` instruction we can remove in the rewriter.
    fn register_for_interval(&mut self, pair: RegLivePair) -> Option<PReg> {
        // if this interval wasn't started by and/or doesn't end with a copy instruction,
        // we don't have anything we can really do.
        let reg = match self.started_by_copy_from.get(&pair) {
            Some(reg) => *reg,
            None => match self.ends_by_copy_to.get(&pair) {
                Some(reg) => *reg,
                None => return self.pool.try_take_any(pair.live(), self.fixed),
            },
        };

        let preferred = match reg.as_preg() {
            // if this is a `x <- %preg` instruction, we try to take that preg
            // so we directly access the value instead of copying it needlessly
            Some(preg) => preg,
            None => {
                let associated = self.reg_to_pair.get(&reg).copied().unwrap();

                // if this is a `x <- y` instruction, try to take `y` as our register
                // if we don't overlap with its live interval.
                //
                // the one edge case is that `y` may have been spilled, in which case we bail
                if !pair.live().overlaps(associated.live()) {
                    if let Some(reg) = self.mapping.get(&associated).copied() {
                        reg
                    } else {
                        // if `associated` was spilled, we bail
                        return self.pool.try_take_any(pair.live(), self.fixed);
                    }
                } else {
                    // if it overlaps we bail
                    return self.pool.try_take_any(pair.live(), self.fixed);
                }
            }
        };

        self
            .pool
            .try_take_specific_register(preferred, pair.live(), self.fixed)
    }

    fn expire_old_intervals<Arch: Architecture>(
        &mut self,
        interval: RegLivePair,
        frame: &mut dyn StackFrame<Arch>,
    ) {
        let mut remove_until = None;

        // go through the active list and find the sublist we need to remove
        for (i, old) in self.active.iter().enumerate() {
            if old.live().ends_after(interval.live()) {
                break;
            }

            remove_until = Some(i);
        }

        // return all the now expired registers to the pool
        if let Some(remove_until) = remove_until {
            let mut v = vec![];

            for i in 0..=remove_until {
                let mapping = self.mapping.get(&self.active[i]).copied().unwrap();

                v.push(mapping);

                self.pool.make_register_available(mapping);
            }

            // remove those active elements. this isn't particularly efficient but this
            // active set will always be very small, since .len() <= R
            self.active.drain(0..=remove_until);
        }
    }

    fn spill_at_interval<Arch: Architecture>(
        &mut self,
        interval: RegLivePair,
        frame: &mut dyn StackFrame<Arch>,
    ) {
        // we can't spill a spill interval without running into trouble, choose another interval to spill
        let (reg, old_preg, reloads) = if interval.live().is_spill_interval() {
            // find the latest non-spill interval
            let (i, _) = self
                .active
                .iter()
                .enumerate()
                .rev()
                .find(|(i, pair)| !pair.live().is_spill_interval())
                .expect("every active slot is a spill interval, don't have enough registers on the target");

            let spill = self.active.remove(i);

            self.spill_other_interval(interval, spill, frame)
        } else {
            let &maybe_spill = self
                .active
                .last()
                .expect("spilling while nothing is active?");

            // if the last active interval ends after our current interval, try to spill that instead.
            if maybe_spill.live().last_used_by() > interval.live().last_used_by()
                && !maybe_spill.live().is_spill_interval()
            {
                let spill = self.active.pop().unwrap();

                self.spill_other_interval(interval, spill, frame)
            } else {
                self.spill(interval, frame)
            }
        };

        let reloads = SmallVec::<[u32; 64]>::from(reloads);

        // create a bunch of miniature intervals at (reload, reload) so we can 'spill everywhere'
        for reload in reloads {
            let micro_interval = LiveInterval::spill(reload);
            let pair = RegLivePair::new(reg, micro_interval);

            // spill everywhere idea: with all of our micro-intervals we are
            // in one of two cases.
            //
            // 1. it was *before* the current `interval` it can just keep using
            //    the register it was already allocated to (through `old_preg`)
            //
            // 2. it is after the current interval, in which case we add it to
            //    the interval queue so it gets allocated later
            if micro_interval.ends_before_without_overlap(interval.live()) {
                // case #1
                self.mapping.insert(
                    pair,
                    old_preg.expect("had interval before but no old allocation"),
                );
            } else {
                // case #2
                self.intervals.push(Reverse(pair));
            }

            // we both need to insert a new tiny interval (if this is after) AND we need to
            // map it as the only spill point (of itself), we might end up spilling
            // one of our spill intervals if we have an absolutely terrible function

            self.spill_points.insert(pair, smallvec![reload]);
        }
    }

    fn spill_other_interval<Arch: Architecture>(
        &mut self,
        interval: RegLivePair,
        spill: RegLivePair,
        frame: &mut dyn StackFrame<Arch>,
    ) -> (Reg, Option<PReg>, &[u32]) {
        let reg = self.mapping.get(&spill).copied().unwrap();

        // take the register that `spill` was mapped to, and remove its mapping
        self.mapping.insert(interval, reg);
        self.mapping.remove(&spill);

        // spill the value and get a new location for it
        self.spills.insert(spill.reg(), frame.spill_slot(8));

        // add interval to the active set
        self.push_active(interval);

        (
            spill.reg(),
            Some(reg),
            self.spill_points.get(&spill).unwrap(),
        )
    }

    fn spill<Arch: Architecture>(
        &mut self,
        interval: RegLivePair,
        frame: &mut dyn StackFrame<Arch>,
    ) -> (Reg, Option<PReg>, &[u32]) {
        debug_assert!(!interval.live().is_spill_interval());

        self.spills.insert(interval.reg(), frame.spill_slot(8));

        (
            interval.reg(),
            None,
            self.spill_points.get(&interval).unwrap(),
        )
    }
}

impl<'a, Arch: Architecture> RegisterAllocator<Arch> for LinearScanRegAlloc<'a> {
    fn allocate(program: &MIRFunction<Arch::Inst>, frame: &mut dyn StackFrame<Arch>) -> Allocation {
        let mut mapping = RegisterMapping::new();
        let mut spills = Vec::default();
        let live = ConservativeLiveIntervals::compute(program, frame);
        let mut lsra = LinearScanRegAlloc::new(
            program.fixed_intervals(),
            live,
            frame.metadata(),
            frame.registers(),
        );

        lsra.lsra(frame);

        macro_rules! rewrites_for_reg {
            ($reg:expr, $lsra:expr, $pp:expr) => {{
                // rewriter expects us to map `%preg` -> `%preg`
                if let Some(preg) = $reg.as_preg() {
                    (None, preg)
                } else {
                    match $lsra.spills.get(&$reg) {
                        Some(loc) => {
                            let current =
                                RegLivePair::new($reg, LiveInterval::spill($pp.offset_of_next()));
                            let register = $lsra.mapping.get(&current).copied().unwrap();

                            (Some(*loc), register)
                        }
                        None => {
                            let interval = $lsra.reg_to_pair.get(&$reg).copied().unwrap();
                            let register = $lsra.mapping.get(&interval).copied().unwrap();

                            (None, register)
                        }
                    }
                }
            }};
        }

        for (pp, inst) in program.all_instructions().iter().program_points() {
            let mut pairs = smallvec![];
            let uses = uses!(inst, frame);
            let defs = defs!(inst, frame);

            for (reg, _) in uses {
                let (loc, preg) = rewrites_for_reg!(reg, lsra, pp);

                pairs.push((reg, preg));

                if let Some(loc) = loc {
                    spills.push((
                        pp,
                        SpillReload::Reload {
                            from: loc,
                            to: preg,
                        },
                    ))
                }
            }

            for (reg, _) in defs {
                let (loc, preg) = rewrites_for_reg!(reg, lsra, pp);

                pairs.push((reg, preg));

                if let Some(loc) = loc {
                    spills.push((
                        ProgramPoint::before(pp.offset_of_next() + 1),
                        SpillReload::Spill {
                            from: preg,
                            to: loc,
                        },
                    ))
                }
            }

            mapping.push(pp, pairs);
        }

        Allocation { mapping, spills }
    }
}

struct RegisterPool {
    priority: SecondaryMap<PReg, i32>,
    register_queue: Vec<PReg>,
    total: usize,
}

impl RegisterPool {
    fn from(metadata: FunctionMetadata, registers: AvailableRegisters) -> Self {
        let mut priority = SecondaryMap::default();
        let mut register_queue = Vec::default();

        // 0 => clobbered, 1 => preserved, 2 => high priority
        let order = [
            registers.clobbered,
            registers.preserved,
            registers.high_priority_temporaries,
        ];

        // we preferred clobbered registers over preserved registers, even in non-leaf
        // functions. the register pool will automatically consider fixed intervals for calls,
        // and the register won't be picked if it overlaps any of them, so clobbered are
        // still better in the general case.
        //
        // preserved will be picked when no clobbered are actually possible to use.
        //
        // order is [clobbered, preserved, high_priority]
        let priorities = [500, 100, 1000];

        for (i, &register_subset) in order.iter().enumerate() {
            for (j, &preg) in register_subset.iter().enumerate().rev() {
                // each register gets a relative priority within its own array, so
                // putting the register first makes the allocator prefer it.
                priority.insert(preg, (priorities[i] - j) as i32);
                register_queue.push(preg);
            }
        }

        // higher priority -> sorted later in the queue
        register_queue.sort_unstable_by_key(|&val| priority[val]);
        register_queue.dedup();

        Self {
            total: register_queue.len(),
            priority,
            register_queue,
        }
    }

    #[inline]
    fn max_simultaneous_live(&self) -> usize {
        self.total
    }

    fn make_register_available(&mut self, preg: PReg) {
        // insert while maintaining sorted order
        match self
            .register_queue
            .binary_search_by_key(&self.priority[preg], |&preg| self.priority[preg])
        {
            Ok(pos) => panic!("somehow duplicated a register"),
            Err(pos) => self.register_queue.insert(pos, preg),
        }
    }

    // tries to take the highest priority register that is valid at the given interval.
    //
    // a register is "valid" at a given interval if no fixed intervals overlap with
    // the interval being allocated for.
    fn try_take_any(&mut self, interval: LiveInterval, fixed: &FixedIntervals) -> Option<PReg> {
        // we review possible candidates in order of decreasing priority
        let mut iter = self.register_queue.iter().enumerate().rev();

        // basic idea: find the highest priority register that isn't defined in
        // a fixed interval that overlaps with `interval`.
        //
        // this is a fallible operation, we may hit a position where the only available registers
        // are taken via fixed registers, so we need to deal with that case at the call site
        let possible_next = loop {
            // if we run out of registers, we're in that fail state detailed above
            let (i, preg) = match iter.next() {
                Some((i, &preg)) => (i, preg),
                None => break None,
            };

            // if none of the fixed intervals for `preg` overlap the current interval, we
            // take this register. if any do, we go to the next one and repeat the process
            if self.is_valid_at(preg, interval, fixed) {
                break Some(i);
            }
        };

        match possible_next {
            // we can't swap_remove here due to needing to maintain sorted order
            // but the array is so small it doesn't really matter at all
            Some(i) => Some(self.register_queue.remove(i)),
            None => None,
        }
    }

    // tries to take a specific preferred register if possible, if it isn't tries to
    // allocate at any possible register just like `try_take_any`
    fn try_take_specific_register(
        &mut self,
        preferred: PReg,
        interval: LiveInterval,
        fixed: &FixedIntervals,
    ) -> Option<PReg> {
        // is preferred even in the queue at all? we can't take that specific
        // one if it's already taken by another interval
        match self
            .register_queue
            .iter()
            .position(move |&reg| reg == preferred)
        {
            // if preferred is both in the queue and valid at the interval,
            // we will take preferred and use it as our target register.
            Some(index) if self.is_valid_at(preferred, interval, fixed) => {
                self.register_queue.remove(index);

                Some(preferred)
            }
            // otherwise we just default to the normal "try and get anything" case
            _ => self.try_take_any(interval, fixed),
        }
    }

    // a register is "valid" at a given interval if no fixed intervals overlap with
    // the interval being allocated for.
    #[inline]
    fn is_valid_at(&self, preg: PReg, interval: LiveInterval, fixed: &FixedIntervals) -> bool {
        !fixed
            .intervals_for(preg)
            .iter()
            .any(move |&fixed| interval.overlaps(fixed))
    }
}
