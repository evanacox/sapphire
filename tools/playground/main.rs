//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2023 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use sapphire::codegen::x86_64::*;
use sapphire::codegen::*;
use sapphire::ir::*;

#[allow(unused)]
fn playground1(module: &mut Module) {
    let builtin_noop = module.declare_function("builtin.x86_64.noop", SigBuilder::new().build());

    let mut b = module.define_function(
        "main",
        SigBuilder::new()
            .params(&[Type::i32(), Type::ptr()])
            .ret(Some(Type::i32()))
            .build(),
    );

    let bb0 = b.create_block("bb0");
    let bb1 = b.create_block("bb1");
    let bb2 = b.create_block("bb2");
    let params = b.append_entry_params(bb0, DebugInfo::fake());
    let v0 = params[0];
    let v1 = params[1];
    b.switch_to(bb0);

    let v2 = b.append().iconst(Type::i32(), 0, DebugInfo::fake());
    let v3 = b.append().icmp(ICmpOp::EQ, v0, v2, DebugInfo::fake());

    let sig = {
        let sig = b.function(builtin_noop).signature().clone();
        b.import_signature(&sig)
    };
    // b.append().call(builtin_noop, sig, &[], DebugInfo::fake());
    b.append().condbr(
        v3,
        BlockWithParams::new(bb2, &[v0, v1]),
        BlockWithParams::to(bb1),
        DebugInfo::fake(),
    );

    b.switch_to(bb1);
    let v4 = b.append().iconst(Type::i32(), 16, DebugInfo::fake());
    let v5 = b.append().iconst(Type::i32(), 0xFF, DebugInfo::fake());
    let v6 = b.append().and(v4, v5, DebugInfo::fake());
    b.append().ret(Some(v6), DebugInfo::fake());

    b.switch_to(bb2);
    b.append_block_param(bb2, Type::i32(), DebugInfo::fake());
    b.append_block_param(bb2, Type::ptr(), DebugInfo::fake());

    let (v7, v8) = {
        let params = b.block_params(bb2);

        (params[0], params[1])
    };

    b.append()
        .br(BlockWithParams::new(bb2, &[v7, v8]), DebugInfo::fake());

    b.define();
}

#[allow(unused)]
fn playground2(module: &mut Module) {
    let mut b = module.define_function(
        "main",
        SigBuilder::new()
            .params(&[Type::i32(), Type::ptr()])
            .ret(Some(Type::i32()))
            .build(),
    );

    let bb0 = b.create_block("bb0");
    let bb1 = b.create_block("bb1");
    let bb2 = b.create_block("bb2");
    let bb3 = b.create_block("bb3");
    let bb4 = b.create_block("bb4");
    let bb5 = b.create_block("bb5");

    b.append_entry_params(bb0, DebugInfo::fake());

    b.switch_to(bb0);
    b.append().br(BlockWithParams::to(bb1), DebugInfo::fake());

    b.switch_to(bb1);
    b.append().br(BlockWithParams::to(bb2), DebugInfo::fake());

    b.switch_to(bb2);
    b.append().br(BlockWithParams::to(bb3), DebugInfo::fake());

    b.switch_to(bb3);
    b.append().br(BlockWithParams::to(bb4), DebugInfo::fake());

    b.switch_to(bb4);
    b.append().br(BlockWithParams::to(bb5), DebugInfo::fake());

    b.switch_to(bb5);
    let v0 = b.append().iconst(Type::i32(), 42, DebugInfo::fake());
    b.append().ret_val(v0, DebugInfo::fake());

    b.define();
}

fn playground3(module: &mut Module) {
    let mut b = module.define_function(
        "main",
        SigBuilder::new()
            .params(&[Type::i32(), Type::ptr()])
            .ret(Some(Type::i32()))
            .build(),
    );

    let bb0 = b.create_block("bb0");
    let params = b.append_entry_params(bb0, DebugInfo::fake());
    let v0 = params[0];

    b.switch_to(bb0);

    let v2 = b.append().iconst(Type::i32(), 1, DebugInfo::fake());
    let mut prev = b.append().iadd(v0, v2, DebugInfo::fake());

    for _ in 0..1000000 {
        let next = b.append().iadd(prev, v2, DebugInfo::fake());

        prev = next;
    }

    b.append().ret_val(prev, DebugInfo::fake());

    b.define();
}

fn main() {
    let mut module = Module::new("playground");

    playground3(&mut module);

    // transforms::verify_module_panic(&module);

    let backend = PresetBackends::x86_64_sys_v_unoptimized(module);
    let string = backend.assembly(X86_64Assembly::GNUIntel);

    println!("{string}");
}
