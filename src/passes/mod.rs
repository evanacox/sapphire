//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Defines the pass infrastructure used by the middle-end of the compiler.
//!
//! Passes are broken down into two categories:
//!
//! 1. Transformations
//! 2. Analyses
//!
//! These two types of passes are used in very different ways, so different
//! infrastructure is defined for both. But, both follow the same basic
//! pattern.
//!
//! Passes at their core are just objects that take in IR and possibly
//! return results:
//!
//! ```
//! # use sapphire::ir::Module;
//! struct Pass { /* ... */ }
//!
//! impl Pass {
//!     fn run(&mut self, ir: &mut Module) { /* ... */ }
//! }
//! ```
//!
//! Of course it's a bit more complicated than that, but at their core,
//! every single pass boils down to roughly that pattern.
//!
//! # Function vs. Module Passes
//! Passes can either operate over an entire module, or they can
//! operate on a single function (the smallest useful unit of IR in SIR).
//! There are different traits to implement depending on what exactly
//! a given pass needs to do.
//!
//! Practically, the only difference is how much IR is visible, and
//! which analysis manager is given by default.
//!
//! # Transform Passes
//! Transform passes are the core of the middle-end of Sapphire.
//! Logically, they are pure functions that map input IR -> output IR.
//!
//! Since passes can be more complicated internally than that, they
//! are allowed to take a `&mut self` to manipulate internal state
//! during the run (and potentially across runs), they should always
//! act as-if they were pure functions. Multiple runs of the same
//! pass over the same IR should produce the same output, regardless
//! of how many times the pass is ran.
//!
//! Analyses can be invalidated by transformations, so all
//! passes that possibly transform IR have to return a set of analyses
//! that they preserve. This could be an empty set, it could be a
//! subset of analyses (e.g. a peephole optimization pass that
//! didn't touch any `condbr`s could preserve any CFG-related
//! analyses), or every analysis (basically only safe if no IR was
//! actually changed).
//!
//! The main two traits used here are [`ModuleTransformPass`] and
//! [`FunctionTransformPass`].
//!
//! # Analysis Passes & Analysis Managers
//! Analysis passes are not able to modify IR, they are only able to
//! observe the IR and use other analyses. They also produce a result
//! of some sort that can be used in other passes (including other
//! analysis passes).
//!
//! These analyses are available through an analysis manager of some
//! sort, depending on the type of pass this is either a
//! [`FunctionAnalysisManager`] or a [`ModuleAnalysisManager`]. Both
//! of these store the results of analyses and will recompute analyses
//! lazily whenever they are invalidated.

mod analysis;
mod manager;
mod transform;

pub use analysis::*;
pub use manager::*;
pub use transform::*;
