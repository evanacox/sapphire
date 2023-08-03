//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

mod dce;
mod domtree;
mod flowgraph;
mod gvn;
mod isel_x86;
mod lsra_x86;
mod mem2reg;
mod optimization_runner;
mod parse;
mod simplifyinst;
mod split_crit_edges;

pub use dce::*;
pub use domtree::*;
pub use flowgraph::*;
pub use gvn::*;
pub use isel_x86::*;
pub use lsra_x86::*;
pub use mem2reg::*;
pub use parse::*;
pub use simplifyinst::*;
pub use split_crit_edges::*;
