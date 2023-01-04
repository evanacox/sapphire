//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Contains the various analysis passes defined in the Sapphire project.
//!
//! These are basically all passes that model the [`FunctionAnalysisPass`] or
//! the [`ModuleAnalysisPass`] traits, and range from debug passes to analyses
//! that are critical for correctness.
//!
//! [`FunctionAnalysisPass`]: crate::passes::FunctionAnalysisPass
//! [`ModuleAnalysisPass`]: crate::passes::ModuleAnalysisPass

mod writer;

pub use writer::*;
