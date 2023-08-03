//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{FunctionDefinition, Value};

/// A location used in parallel copy scheduling.
///
/// This is either just a reference to a [`Value`](crate::ir::Value) or
/// it's an anonymous temporary identified by the `u32` it holds.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum ParallelCopyLocation {
    /// A reference to a value (and its associated storage)
    Normal(Value),
    /// A reference to an anonymous temporary, necessary to break cycles.
    /// The [`Value`] is the value it's created to break a cycle for,
    /// and thus this can be queried for type info and whatnot.
    Temporary(u64, Value),
}

impl ParallelCopyLocation {
    /// Gets the associated value, no matter what state `self` is in.
    #[inline]
    pub fn associated_val(self) -> Value {
        match self {
            Self::Normal(v) => v,
            Self::Temporary(_, v) => v,
        }
    }

    #[inline]
    fn new_temporary_from(old: ParallelCopyLocation, id: u64) -> Self {
        Self::Temporary(id, old.associated_val())
    }
}

/// Given a list of block parameters and arguments being passed as the new
/// values of those block parameters, this schedules them correctly in a way
/// that doesn't fall into the swap problem.
///
/// The resulting `Vec` stores them in `(a, b)` pairs modeling the copy `b <- a`.
pub fn schedule_parallel_copies(
    params: &[Value],
    args: &[Value],
    def: &FunctionDefinition,
) -> Vec<(ParallelCopyLocation, ParallelCopyLocation)> {
    // this set will be small, so we use a vec for the overall storage of "to-do"
    // parallel copy pairs. this allows us to efficiently pop and take the next
    let mut parallel_copies = Vec::default();
    let mut temp_id = 0u64;

    // the sequential set of copies that needs to be emitted
    let mut seq = Vec::default();

    for (&source, &dest) in args.iter().zip(params.iter()) {
        // we ignore `a <- a` copies for this algorithm, they don't actually
        // need to be emitted at all (since by definition `a == a` already).
        if source == dest {
            continue;
        }

        let source = ParallelCopyLocation::Normal(source);
        let dest = ParallelCopyLocation::Normal(dest);

        parallel_copies.push((source, dest));
    }

    //
    // basic idea: we have a set of copies remaining to work on in `parallel_copies`
    //
    // 1. try to remove any copies without a cycle (`b <- a` where there are no copies s.t. `c <- b`)
    //    and put them in our sequential result list, repeat until all copies have a cycle
    // 2. introduce one temporary to break a cycle, add a new copy to the active set
    //
    // in the general case, all of our work gets done in #1. if we hit a swap problem
    // situation, #2 comes into play to break cycles and allow #1 to keep working
    //
    while !parallel_copies.is_empty() {
        let mut i = 0;
        let mut any_trivial = false;

        // try to find any pairs that aren't in a cycle, we can just emit those as-is
        // this will be the vast majority of them unless we hit a swap situation
        let found = loop {
            if i >= parallel_copies.len() {
                break any_trivial;
            }

            let (a, b) = parallel_copies[i];

            // given `b <- a`, if there is no pair `c <- b` then there isn't a cycle
            // and we can just emit the copy directly
            if !parallel_copies.iter().any(|(source, dest)| source == &b) {
                seq.push((a, b));
                parallel_copies.swap_remove(i);
                any_trivial = true;
            }

            i += 1;
        };

        // if we didn't find any, every copy in `parallel_copies` is a cycle so we
        // need to break one of them before trying the above process again
        if !found {
            let (a, b) = parallel_copies
                .pop()
                .expect("not empty and didn't remove anything, somehow empty?");

            // create a new variable a'
            temp_id += 1;
            let a_prime = ParallelCopyLocation::new_temporary_from(a, temp_id);

            // we "replace" `b <- a` with `a' <- a` and `b <- a'`
            seq.push((a, a_prime));
            parallel_copies.push((a_prime, b));
        }
    }

    seq
}
