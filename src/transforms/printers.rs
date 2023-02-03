//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{DominatorTreeAnalysis, ModuleStringifyAnalysis};
use crate::ir::{Block, Function, Module};
use crate::pass::{
    FunctionAnalysisManager, FunctionTransformPass, ModuleAnalysisManager, ModuleTransformPass,
    PreservedAnalyses,
};
use crate::utility;
use std::io;

/// Wrapper pass that prints out a textual representation of a [`DominatorTree`].
///
/// [`DominatorTree`]: crate::analysis::DominatorTree
pub struct DominatorTreeWriterPass {
    out: Box<dyn io::Write>,
}

impl DominatorTreeWriterPass {
    /// Shorthand for a writer that prints to [`std::io::stdout`].
    pub fn stdout() -> Self {
        Self::with_writer(io::stdout())
    }

    /// Shorthand for a writer that prints to [`std::io::stderr`].
    pub fn stderr() -> Self {
        Self::with_writer(io::stderr())
    }

    /// Creates an instance of the pass with a given writer.
    ///
    /// This writer will be where the module is printed out when the analysis
    /// is run over the IR.
    pub fn with_writer<T: io::Write + 'static>(writer: T) -> Self {
        Self {
            out: Box::new(writer),
        }
    }
}

impl FunctionTransformPass for DominatorTreeWriterPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        let domtree = am.get::<DominatorTreeAnalysis>(func);
        let strings = func.ctx().strings();
        let def = func
            .definition()
            .expect("expected definition to print domtree");
        let print = |bb: Block| strings.get(def.dfg.block(bb).name()).unwrap().to_owned();
        let result = utility::stringify_tree(&*domtree, print);

        writeln!(self.out, "{result}").expect("should have been able to write");

        PreservedAnalyses::all()
    }
}

/// This is a pass that writes out a textual representation of a module
/// to a given stream.
pub struct ModuleWriterPass {
    out: Box<dyn io::Write>,
}

impl ModuleWriterPass {
    /// Shorthand for a writer that prints to [`std::io::stdout`].
    pub fn stdout() -> Self {
        Self::with_writer(io::stdout())
    }

    /// Shorthand for a writer that prints to [`std::io::stderr`].
    pub fn stderr() -> Self {
        Self::with_writer(io::stderr())
    }

    /// Creates an instance of the pass with a given writer.
    ///
    /// This writer will be where the module is printed out when the analysis
    /// is run over the IR.
    pub fn with_writer<T: io::Write + 'static>(writer: T) -> Self {
        Self {
            out: Box::new(writer),
        }
    }
}

impl ModuleTransformPass for ModuleWriterPass {
    fn run(&mut self, module: &mut Module, am: &mut ModuleAnalysisManager) -> PreservedAnalyses {
        let writer = am.get::<ModuleStringifyAnalysis>(module);

        self.out
            .write_all(writer.module().as_bytes())
            .expect("unable to write module to writer");

        PreservedAnalyses::all()
    }
}
