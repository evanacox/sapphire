//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{ControlFlowGraph, DominatorTree};
use crate::codegen::{Architecture, Target, ABI};
use crate::ir::{DataFlowGraph, Func, Function, Module, TypePool, Value};
use crate::pass::{ModuleAnalysisManager, ModuleTransformPass, PreservedAnalyses};
use std::marker::PhantomData;

/// Demotion pass that moves any aggregates (arrays, structures) that are "too big"
/// for a specific arch/abi configuration to deal with in registers onto the stack.
///
/// This definition of "too big" is based on what the ABI determines should be passed
/// on the stack vs. passed in registers. If the ABI has bad decisions here, this
/// pass will generate bad code.
///
/// This performs both modifications on the function signatures themselves and on the
/// values. Functions that accept aggregates will be transformed into functions that
/// accept pointers, and the values themselves will be replaced by stores/loads from
/// stack allocations.
///
/// If an aggregate is defined as "too big," it is given a unique stack slot, and
/// operations with that aggregate are transformed
pub struct LegalizeAggregatesForABI<Arch, Abi>
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    target: Target<Arch, Abi>,
    _unused: PhantomData<fn() -> (Arch, Abi)>,
}

impl<Arch, Abi> LegalizeAggregatesForABI<Arch, Abi>
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    /// Creates an instance of the legalizer
    ///
    /// The legalizer relies on `target` being configured for the module that will
    /// be legalized.
    pub fn new(target: Target<Arch, Abi>) -> Self {
        Self {
            target,
            _unused: PhantomData::default(),
        }
    }

    fn demote_aggregates(
        &mut self,
        func: &mut Function,
        cfg: &ControlFlowGraph,
        domtree: &DominatorTree,
    ) {
        //
    }

    fn find_funcs_with_agg_params(module: &Module) -> Vec<Func> {
        module
            .functions()
            .filter(|func| {
                module
                    .function(*func)
                    .signature()
                    .params()
                    .iter()
                    .any(|(ty, _)| ty.is_aggregate())
            })
            .collect()
    }

    fn should_demote(&self, ctx: &TypePool, dfg: &DataFlowGraph, value: Value) -> bool {
        let ty = dfg.ty(value);

        if !ty.is_aggregate() {
            return false;
        }

        false
    }
}

impl<Arch, Abi> ModuleTransformPass for LegalizeAggregatesForABI<Arch, Abi>
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    fn run(&mut self, module: &mut Module, am: &mut ModuleAnalysisManager) -> PreservedAnalyses {
        todo!()
    }
}
