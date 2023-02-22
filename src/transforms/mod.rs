//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Defines the "transform" passes in SIR's infrastructure.
//!
//! These are the passes that can (potentially) modify SIR, and don't
//! actually logically yield a result.
//!
//! Some of these "transforms" are not actually transformations (e.g.
//! the verify pass is a "transform pass" even though it manipulates no IR),
//! but most of them are. All of them logically yield no result except
//! the IR that exists after they run.

pub mod common;

mod dce;
mod gvn;
mod mem2reg;
mod printers;
mod sccp;
mod simplifycfg;
mod simplifyinst;
mod verify;

pub use dce::*;
pub use gvn::*;
pub use mem2reg::*;
pub use printers::*;
pub use sccp::*;
pub use simplifycfg::*;
pub use simplifyinst::*;
pub use verify::*;
