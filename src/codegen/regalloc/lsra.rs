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
use crate::codegen::{
    Allocation, Architecture, AvailableRegisters, ConservativeLiveIntervals, FixedIntervals,
    LiveInterval, MIRFunction, MachInst, PReg, ProgramPointsIterator, Reg, RegisterAllocator,
    RegisterMapping, StackFrame, VariableLocation,
};
use crate::ir::FunctionMetadata;
use crate::utility::SaHashMap;
use smallvec::{smallvec, SmallVec};
use std::mem;

/// A linear scanning based register allocator
///
/// This allocator is a balance between compile time performance and output
/// quality, it provides a balance of both.
pub struct LinearScanRegAlloc<'a> {
    active: Vec<LiveInterval>,
    intervals: Vec<LiveInterval>,
    fixed: &'a FixedIntervals,
    original_int_to_reg: SaHashMap<LiveInterval, Reg>,
    original_reg_to_int: SaHashMap<Reg, LiveInterval>,
    mapping: SaHashMap<LiveInterval, PReg>,
    started_by_copy: SaHashMap<LiveInterval, Reg>,
    reload_points: SaHashMap<LiveInterval, SmallVec<[u32; 4]>>,
    spills: SaHashMap<LiveInterval, VariableLocation>,
    pool: RegisterPool,
}

impl<'a> LinearScanRegAlloc<'a> {
    fn new(
        fixed: &'a FixedIntervals,
        mut live: ConservativeLiveIntervals,
        metadata: FunctionMetadata,
        available: AvailableRegisters,
    ) -> Self {
        let mut intervals = Vec::default();
        let mut original_int_to_reg = SaHashMap::default();
        let mut original_reg_to_int = SaHashMap::default();
        let mut started_by_copy = SaHashMap::default();
        let mut reload_points = SaHashMap::default();

        for (reg, interval) in live.intervals() {
            original_int_to_reg.insert(interval, reg);
            original_reg_to_int.insert(reg, interval);
            intervals.push(interval);

            if let Some(reg) = live.started_by_copy(reg) {
                started_by_copy.insert(interval, reg);
            }
        }

        // we have to do this after, because we're using `take_reload_points` to avoid
        // needing to re-create the SmallVec objects
        for &interval in intervals.iter() {
            let &reg = original_int_to_reg.get(&interval).unwrap();

            reload_points.insert(interval, live.take_reload_points(reg));
        }

        // intervals need to be sorted by increasing start point, `LiveInterval`
        // implements `Ord` in that way so we can just sort normally
        intervals.sort_unstable();

        Self {
            intervals,
            fixed,
            original_int_to_reg,
            original_reg_to_int,
            started_by_copy,
            reload_points,
            active: Vec::default(),
            mapping: SaHashMap::default(),
            spills: SaHashMap::default(),
            pool: RegisterPool::from(metadata, available),
        }
    }
}

impl<'a> LinearScanRegAlloc<'a> {
    fn lsra<Arch: Architecture>(&mut self, frame: &mut dyn StackFrame<Arch>) {
        let end = self.intervals.last().unwrap().last_used_by();
        let intervals = mem::take(&mut self.intervals);

        for &interval in intervals.iter() {
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

    fn maybe_allocate<Arch: Architecture>(
        &mut self,
        interval: LiveInterval,
        frame: &mut dyn StackFrame<Arch>,
    ) {
        match self.register_for_interval(interval) {
            // if we did get a valid register, mark this interval as active
            // and record the register mapping for this interval
            Some(reg) => {
                self.mapping.insert(interval, reg);
                self.active.push(interval);

                // sort in order of increasing end points, needed for ExpireOldIntervals
                self.active
                    .sort_unstable_by_key(|interval| interval.last_used_by())
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
    fn register_for_interval(&mut self, interval: LiveInterval) -> Option<PReg> {
        // if this interval wasn't started by a copy instruction,
        // we don't have anything we can really do.
        let reg = match self.started_by_copy.get(&interval) {
            Some(reg) => *reg,
            None => return self.pool.try_take_any(interval, self.fixed),
        };

        let preferred = match reg.as_preg() {
            // if this is a `x <- %preg` instruction, we try to take that preg
            // so we directly access the value instead of copying it needlessly
            Some(preg) => preg,
            None => {
                let associated = self.original_reg_to_int.get(&reg).copied().unwrap();

                // if this is a `x <- y` instruction, try to take `y` as our register
                // if we don't overlap with its live interval.
                //
                // we can assume `y` is already allocated due to it being before us.
                if !interval.overlaps(associated) {
                    self.mapping.get(&associated).copied().unwrap()
                } else {
                    // if it overlaps, we just bail and try to take anything
                    return self.pool.try_take_any(interval, self.fixed);
                }
            }
        };

        return self
            .pool
            .try_take_specific_register(preferred, interval, self.fixed);
    }

    fn expire_old_intervals<Arch: Architecture>(
        &mut self,
        interval: LiveInterval,
        frame: &mut dyn StackFrame<Arch>,
    ) {
        let mut remove_until = None;

        // go through the active list and find the sublist we need to remove
        for (i, old) in self.active.iter().enumerate() {
            if old.ends_after(interval) {
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
        interval: LiveInterval,
        frame: &mut dyn StackFrame<Arch>,
    ) {
        let spill = self
            .active
            .last()
            .expect("spilling while nothing is active?");

        if spill.last_used_by() > interval.last_used_by() {
            let vreg = self.original_int_to_reg.get(spill).copied().unwrap();
            let reg = self.mapping.get(spill).copied().unwrap();
            let spill = self.active.pop().unwrap();

            self.mapping.insert(interval, reg);
            self.spills.insert(spill, frame.spill_slot(8));

            for &reload in self.reload_points.get(&spill).unwrap() {}
        } else {
        }
    }
}

impl<'a, Arch: Architecture> RegisterAllocator<Arch> for LinearScanRegAlloc<'a> {
    fn allocate(program: &MIRFunction<Arch::Inst>, frame: &mut dyn StackFrame<Arch>) -> Allocation {
        let mut mapping = RegisterMapping::new();
        let live = ConservativeLiveIntervals::compute(program, frame);
        let mut obj = LinearScanRegAlloc::new(
            program.fixed_intervals(),
            live,
            frame.metadata(),
            frame.registers(),
        );

        obj.lsra(frame);

        for (pp, inst) in program.all_instructions().iter().program_points() {
            let mut pairs = smallvec![];
            let uses = uses!(inst, frame);
            let defs = defs!(inst, frame);

            for &(reg, _) in uses.iter().chain(defs.iter()) {
                // rewriter expects us to map `%preg` -> `%preg`
                if let Some(preg) = reg.as_preg() {
                    pairs.push((reg, preg))
                } else {
                    let interval = obj.original_reg_to_int.get(&reg).unwrap();
                    let preg = obj.mapping.get(interval).copied().unwrap();

                    pairs.push((reg, preg));
                }
            }

            mapping.push(pp, pairs);
        }

        Allocation {
            mapping,
            spills: vec![],
        }
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

        // if we're a leaf function, prefer clobbered registers over preserved registers.
        // 0 => clobbered priority value, 1 => preserved priority value,
        // 2 => high priority priority value
        let priorities = if metadata.is_leaf {
            [200, 100, 1000]
        } else {
            [100, 200, 1000]
        };

        for (i, &register_subset) in order.iter().enumerate() {
            for (j, &preg) in register_subset.iter().enumerate().rev() {
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
