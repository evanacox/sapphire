//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::subtest::{Subtest, TestResult};
use sapphire::analysis::{ControlFlowGraph, DominatorTree};
use sapphire::ir::Block;
use sapphire::{transforms, utility};

fn domtree_test(name: &str, contents: &str) -> TestResult {
    let module = match sapphire::parse_sir(name, contents) {
        Ok(module) => module,
        Err(e) => return TestResult::CompileError(e),
    };

    transforms::verify_module_panic(&module);

    let mut result = String::default();

    for func in module.functions() {
        let func = module.function(func);

        if !func.is_decl() {
            let cfg = ControlFlowGraph::compute(func);
            let strings = func.ctx().strings();
            let def = func
                .definition()
                .expect("expected definition to print domtree");
            let print = |bb: Block| strings.get(def.dfg.block(bb).name()).unwrap().to_owned();
            let domtree = DominatorTree::compute(func, &cfg);

            result += &utility::stringify_tree(&domtree, print);
        }
    }

    TestResult::Output(result)
}

pub const fn domtree_subtest() -> Subtest {
    Subtest::new(&["domtree"], domtree_test)
}
