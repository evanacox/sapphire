//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use std::sync::atomic::{AtomicBool, Ordering};

/// A TTAS (test and test-and-set) spin-lock.
///
/// The mutex has the correct acquire/release semantics on lock/unlock, and will try
/// to inform the CPU when inside the spin-loop with [`core::hint::spin_loop`].
///
/// This is intended for uses where the time spent holding the lock is miniscule, e.x.
/// for use with the preserved analyses global lock (in which case the lock is only held to
/// perform a single store). **This is not a general purpose mutex.**
///
/// A simple mutex based around a spin-lock and an atomic flag. While it's not particularly
/// efficient, but it works without any support (or lack thereof) from a runtime/operating system
///
/// This implementation will try to use architecture-specific instructions to improve power efficiency
/// of cores while they're waiting, using something like the x86 `pause` instruction or the
/// arm `yield` instruction while inside the wait loop to inform the CPU of what's going on.
#[repr(transparent)]
pub struct SpinMutex {
    flag: AtomicBool,
}

impl SpinMutex {
    /// Creates a new unlocked [`SpinMutex`].
    pub const fn new() -> Self {
        Self {
            flag: AtomicBool::new(false),
        }
    }

    /// Locks the mutex, potentially waiting if it's already locked. This follows
    /// the semantics of `Ordering::Acquire`.
    pub fn lock(&self) {
        // our goal here is to prevent refreshing caches on potentially contended locks
        // when multiple threads are going for it. therefore, we need to reduce writes to
        // a bare minimum.
        loop {
            // check first, if the lock isn't taken we get to it with 1 less load and if it
            // isn't, we aren't in any hurry to get into the test loop anyway
            if !self.flag.swap(true, Ordering::Acquire) {
                break;
            }

            // inner loop, reduces number of writes and therefore reduces
            // the need to refresh caches for every core 24/7
            while self.flag.load(Ordering::Relaxed) {
                // hint to the CPU what we're doing, may help or may not. almost
                // certainly doesn't hurt though
                core::hint::spin_loop();
            }
        }
    }

    /// Unlocks the mutex. This follows the semantics of `Ordering::Release`.
    pub fn unlock(&self) {
        self.flag.store(false, Ordering::Release);
    }
}

/// Effectively the same thing as [`SpinMutex`], except it doesn't call [`core::hint::spin_loop`].
/// This avoids potential tiny slowdowns from a `pause` or `yield` instruction, but also harms
/// power efficiency and hyper-threading.
///
/// Do not use this unless all of the following are true:
///
///   1. Your lock is highly contended
///   2. You cannot reduce contention on the lock
///   3. You care about a couple of ns of loss on lock acquisition
///   4. You are perfectly fine with a hyper-thread on the same core being starved for load-store unit time
///   5. You don't care about the potentially large amount of wasted power as the CPU burns cycles trying to
///      predict/prefetch/whatever on a 3 instruction loop.
#[repr(transparent)]
pub struct RawSpinMutex {
    flag: AtomicBool,
}

impl RawSpinMutex {
    /// Creates a new unlocked [`RawSpinMutex`].
    pub const fn new() -> Self {
        Self {
            flag: AtomicBool::new(false),
        }
    }

    /// Locks the mutex, potentially waiting if it's already locked. This follows
    /// the semantics of `Ordering::Acquire`.
    pub fn lock(&self) {
        loop {
            if !self.flag.swap(true, Ordering::Acquire) {
                break;
            }

            #[allow(clippy::missing_spin_loop)]
            while self.flag.load(Ordering::Relaxed) { /* explicitly not using spin-hint */ }
        }
    }

    /// Unlocks the mutex. This follows the semantics of `Ordering::Release`.
    pub fn unlock(&self) {
        self.flag.store(false, Ordering::Release);
    }
}
