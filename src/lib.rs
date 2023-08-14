//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

#![allow(dead_code)]
#![deny(
    unreachable_pub,
    missing_docs,
    missing_abi,
    rust_2018_idioms,
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links
)]
#![allow(unused_variables)]

//! # Sapphire
//!
//! These are the basic APIs for building, manipulating and emitting SIR.

pub mod analysis;
pub mod arena;
pub mod codegen;
pub mod ir;
pub mod pass;
pub mod reader2;
pub mod transforms;
pub mod utility;
pub mod vm;

#[cfg(feature = "dev-tools")]
pub mod cli;

use crate::analysis::{
    ControlFlowGraphAnalysis, DominanceFrontierAnalysis, DominatorTreeAnalysis,
    ModuleStringifyAnalysis,
};
use crate::pass::{
    FunctionAnalysisManager, FunctionAnalysisManagerModuleProxy, FunctionToModulePassAdapter,
    ModuleAnalysisManager, ModulePassManager, ModuleTransformPass,
};
use crate::transforms::{
    AggressiveDCEPass, DominatorTreeWriterPass, GVNPass, Mem2RegPass, ModuleWriterPass, SCCPPass,
    SimplifyCFGPass, SimplifyInstPass, SplitCriticalEdgesPass, VerifyModulePass,
};

pub use reader2::parse_sir;

/// A helper function that handles "run these passes specified by the user" in a way that multiple
/// tools can use.
///
/// This is not intended to be used for pre-determined pass pipelines, but is useful for tools
/// that work in a similar way to `siro`.
///
/// - `verify` is whether to insert verify passes between all passes
/// - `passes` is the user-specified list of passes
/// - `extra` are any extra passes that must be run after `passes` that are provided by the tool
pub fn run_passes(
    module: &mut ir::Module,
    verify: bool,
    passes: &[String],
    extra: &[&'static str],
) {
    let mut fam = FunctionAnalysisManager::new();
    fam.add_analysis(ControlFlowGraphAnalysis);
    fam.add_analysis(DominatorTreeAnalysis);
    fam.add_analysis(DominanceFrontierAnalysis);

    let mut mam = ModuleAnalysisManager::new();
    mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));
    mam.add_analysis(ModuleStringifyAnalysis);

    let mut mpm = ModulePassManager::new();

    if verify {
        mpm.add_pass(VerifyModulePass);
    }

    for pass in passes
        .iter()
        .cloned()
        .chain(extra.iter().map(|s| s.to_string()))
    {
        match pass.as_str() {
            "mem2reg" => mpm.add_pass(FunctionToModulePassAdapter::adapt(Mem2RegPass)),
            "dce" => mpm.add_pass(FunctionToModulePassAdapter::adapt(AggressiveDCEPass)),
            "gvn" => mpm.add_pass(FunctionToModulePassAdapter::adapt(GVNPass)),
            "simplifyinst" => mpm.add_pass(FunctionToModulePassAdapter::adapt(SimplifyInstPass)),
            "simplifycfg" => mpm.add_pass(FunctionToModulePassAdapter::adapt(SimplifyCFGPass)),
            "sccp" => mpm.add_pass(FunctionToModulePassAdapter::adapt(SCCPPass)),
            "split-crit-edges" => {
                mpm.add_pass(FunctionToModulePassAdapter::adapt(SplitCriticalEdgesPass))
            }
            "domtree-stdout" => mpm.add_pass(FunctionToModulePassAdapter::adapt(
                DominatorTreeWriterPass::stdout(),
            )),
            "domtree-stderr" => mpm.add_pass(FunctionToModulePassAdapter::adapt(
                DominatorTreeWriterPass::stderr(),
            )),
            "module-stdout" => mpm.add_pass(ModuleWriterPass::stdout()),
            "module-stderr" => mpm.add_pass(ModuleWriterPass::stderr()),
            _ => {
                unreachable!()
            }
        }

        if verify {
            mpm.add_pass(VerifyModulePass);
        }
    }

    mpm.run(module, &mut mam);
}
