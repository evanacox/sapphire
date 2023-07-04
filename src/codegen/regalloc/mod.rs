//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! This module defines the interface for a register allocator, along with
//! several register allocators that have various levels of compile-time
//! performance and codegen quality.
//!
//! # Allocators
//!
//! ## Everything On The Stack
//!
//!
//!
//! ## Linear Scan
//!
//! The [`LinearScanRegAlloc`] is the register allocator intended to be used
//! in unoptimized-ish settings, as it is reasonably fast to actually execute
//! and generates decent code at the end.
//!
//! ## Graph Coloring
//!
//! TODO
//!
//! This is a much more complex register allocator that typically generates
//! better code, but it takes significantly longer to execute. This should
//! be used at the end of optimized pipelines where compile time is
//! irrelevant.

mod allocator;
mod irc;
mod liveness;
mod lsra;
mod stack;

pub use allocator::*;
pub use irc::GraphColoringRegAlloc;
pub use liveness::Liveness;
pub use lsra::LinearScanRegAlloc;
pub use stack::StackRegAlloc;
