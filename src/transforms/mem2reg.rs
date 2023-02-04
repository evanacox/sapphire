//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::*;
use crate::ir::*;
use crate::pass::{FunctionAnalysisManager, FunctionTransformPass, PreservedAnalyses};
use crate::transforms::common::rewrite_pad_branch_argument;
use crate::utility::{IntoTree, SaHashMap, SaHashSet};
use smallvec::{smallvec, SmallVec};

/// Promotes `alloca`s that only have `load`s and `store`s as uses into registers.
/// This is effectively an SSA construction pass, it promotes memory operations into
/// SSA values and φ nodes.  
///
/// This pass generates *minimal* SSA, not *pruned* SSA. You likely want to run
/// DCE after this pass for pruned SSA.
///
/// # Limitations:
/// - This will not promote any local memory that has multiple types stored into it,
///   e.g. an i64 that has the value of an f64 stored into it will just be ignored.
///
/// - Any `alloca` that is leaked in **any way** is not promoted. An `alloca`
///   must only have `load`s and `store`s as uses, even passing the `alloca`
///   through φ nodes will cause it to be ignored.
///
/// - Right now, this pass does not treat `elemptr` as a `load`/`store`, and will
///   just ignore any `alloca`s that are used in an `elemptr`. If you want aggregates to
///   be promoted, they need to be created via `insert`s and then `store`d into the memory.
pub struct Mem2RegPass;

impl FunctionTransformPass for Mem2RegPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        let cfg = am.get::<ControlFlowGraphAnalysis>(func);
        let domtree = am.get::<DominatorTreeAnalysis>(func);
        let df = am.get::<DominanceFrontierAnalysis>(func);

        mem2reg(func, &cfg, &domtree, &df);

        let mut preserved = PreservedAnalyses::none();

        preserved.preserve::<ControlFlowGraphAnalysis>();
        preserved.preserve::<DominatorTreeAnalysis>();
        preserved.preserve::<DominanceFrontierAnalysis>();

        preserved
    }
}

/// Promotes function-local memory (that doesn't escape) into φ nodes where possible.
///
/// This is effectively an SSA construction pass, but because SIR is always in SSA form
/// this is also a register promotion pass.
pub fn mem2reg(
    func: &mut Function,
    cfg: &ControlFlowGraph,
    domtree: &DominatorTree,
    df: &DominanceFrontier,
) {
    let mut cursor = FuncCursor::over(func);
    let allocas = find_promotable_allocas(&mut cursor, domtree);
    let phis = insert_phis(&mut cursor, &allocas, df);

    rename_variables(&mut cursor, &allocas, &phis, cfg, domtree);

    for &alloca in allocas.keys() {
        let inst = cursor.value_to_inst(alloca).unwrap();

        cursor.goto_inst(inst);
        cursor.remove_inst();
    }
}

// finds all of the allocas that are actually promotable, along with their definition
// and the type that the alloca was defined with.
fn find_promotable_allocas(
    cursor: &mut FuncCursor<'_>,
    domtree: &DominatorTree,
) -> SaHashMap<Value, (Type, SmallVec<[Inst; 4]>)> {
    // allocas is our result, escaped is scratch storage for our "find usages that
    // make it impossible to promote" in our inner loop
    let mut allocas = SaHashMap::default();
    let mut not_promotable = SmallVec::<[Value; 16]>::default();

    // basic idea: we scan through the function in reverse postorder to see
    // defs before uses. We find any allocas and we record them in `allocas`,
    // along with their type and any stores to that alloca (stores = "defs" of
    // the "variable" that we are promoting, in SSA construction terms)
    for block in domtree.reverse_postorder() {
        cursor.goto_before(block);

        while let Some(inst) = cursor.next_inst() {
            if let InstData::Alloca(alloca) = cursor.inst_data(inst) {
                allocas.insert(
                    cursor.inst_to_result(inst).unwrap(),
                    (alloca.alloc_ty(), smallvec![]),
                );

                continue;
            }

            // if an instruction has a side effect and uses the value of
            // one of our allocas, we consider it to have "escaped."
            let data = cursor.inst_data(inst);
            let operands = cursor.inst_data(inst).operands();

            // if the instruction has no pointee operands, we just skip over it.
            if !operands.iter().any(|val| cursor.ty(*val).is_ptr()) {
                continue;
            }

            // we go through all of our allocas and see if the instruction does something
            // that makes it non-promotable.
            //
            // the reason we can't break out of this after the first match is we may potentially
            // be using multiple allocas in the same instruction
            for (&alloca, (ty, defs)) in allocas.iter_mut() {
                if operands.contains(&alloca) {
                    match data {
                        InstData::Store(store) => {
                            if store.pointer() != alloca || *ty != cursor.ty(store.stored()) {
                                not_promotable.push(alloca);
                            } else {
                                defs.push(inst)
                            }
                        }
                        InstData::Load(load) => {
                            if load.result_ty().unwrap() != *ty {
                                not_promotable.push(alloca);
                            }
                        }
                        // any other usage besides a load/store, we assume the pointer escaped
                        // so we just don't promote that at all
                        _ => not_promotable.push(alloca),
                    }
                }
            }

            // `not_promotable` is just scratch storage because we can't mutate `allocas` above
            for alloca in not_promotable.drain(..) {
                allocas.remove(&alloca);
            }
        }
    }

    allocas
}

// runs the φ-insertion algorithm, and returns the phi nodes that were inserted at
// given join points.
//
// the return value maps φ node -> alloca it is for
fn insert_phis(
    cursor: &mut FuncCursor<'_>,
    allocas: &SaHashMap<Value, (Type, SmallVec<[Inst; 4]>)>,
    df: &DominanceFrontier,
) -> SaHashMap<Value, Value> {
    // maps an alloca and a block to a phi node for that alloca.
    // this is intended to map alloca -> phi for blocks where the phi was added
    let mut phis = SaHashMap::default();

    // we need a consistent order for these to be inserted, so instead of directly iterating
    // over the hash table we instead copy keys into a vec and then sort it.
    //
    // the keys are integers anyway and this will be a very small vec, should be cheap
    let mut alloca_keys: SmallVec<[Value; 16]> = allocas.keys().copied().collect();
    alloca_keys.sort();

    for alloca in alloca_keys {
        let (ty, defs) = &allocas[&alloca];
        let mut phis_added = SaHashSet::default();
        let mut contains_defs = SaHashSet::default();

        for &def in defs.iter() {
            contains_defs.insert(cursor.inst_block(def));
        }

        // go through all the blocks where we store to the alloca, and find
        // join points after those blocks from the dominance frontier
        while let Some(&block) = contains_defs.iter().next() {
            contains_defs.remove(&block);

            for &bb in df.frontier(block) {
                // if we haven't already added a phi for this variable yet for this
                // particular join point, add the phi and record it.
                if !phis_added.contains(&bb) {
                    let dbg = cursor.dfg().debug(alloca).strip_name();
                    let phi = cursor.def_mut().dfg.append_block_param(bb, *ty, dbg);

                    phis.insert(phi, alloca);
                    phis_added.insert(bb);

                    // if `bb` is not a block that provides a def for `alloca`
                    if !defs.iter().any(|&def| cursor.inst_block(def) == bb) {
                        contains_defs.insert(bb);
                    }
                }
            }
        }
    }

    phis
}

enum Memory {
    Def(StoreInst),
    Use(LoadInst),
}

// Gets the closest (dominating) definition for a given alloca. If there is none,
// an `undef` is inserted as the definition and is then returned.
fn nearest_reaching_def(
    cursor: &mut FuncCursor<'_>,
    alloca: Value,
    ty: Type,
    dbg: DebugInfo,
    defs: &mut SaHashMap<Value, SmallVec<[Value; 4]>>,
) -> Value {
    let stack = defs.get_mut(&alloca).unwrap();

    match stack.last().copied() {
        Some(v) => v,
        None => {
            let undef = cursor.insert().undef(ty, dbg.strip_name());

            stack.push(undef);

            undef
        }
    }
}

fn rename_variables_recursive(
    cursor: &mut FuncCursor<'_>,
    phis: &SaHashMap<Value, Value>,
    reaching_def: &mut SaHashMap<Value, SmallVec<[Value; 4]>>,
    cfg: &ControlFlowGraph,
    domtree: &DominatorTree,
) {
    let bb = cursor.current_block().unwrap();
    let mut defs = SmallVec::<[Value; 12]>::default();

    // first task is to update reaching_def if any of our block's φ nodes are
    // actually definitions for a variable in this block
    for &phi in cursor.block_params(bb) {
        if let Some(&alloca) = phis.get(&phi) {
            defs.push(alloca);
            reaching_def.get_mut(&alloca).unwrap().push(phi);
        }
    }

    // this is the main renaming loop, we remove loads and replace their uses with the
    // closest reaching definition, and we remove stores and set the value they were storing
    // as the most recent definition
    while let Some(inst) = cursor.next_inst() {
        // needed to clone so cursor wasn't borrowed, we need to mutate it
        let op = match cursor.inst_data(inst) {
            InstData::Load(load) if reaching_def.contains_key(&load.pointer()) => {
                Memory::Use(*load)
            }
            InstData::Store(store) if reaching_def.contains_key(&store.pointer()) => {
                defs.push(store.pointer());
                Memory::Def(*store)
            }
            _ => continue,
        };

        match op {
            // by this point, we can assume that any stores to that alloca
            // that are in `reaching_def` are actually allocas we can promote.
            // we checked earlier to make sure
            Memory::Use(load) => {
                // if there is no closest definition, we insert an `undef` instruction
                // and use that as our new def. otherwise, we replace the load's uses
                // with that closest definition and remove the load
                let val = cursor.inst_to_result(inst).unwrap();
                let closest_def = nearest_reaching_def(
                    cursor,
                    load.pointer(),
                    load.result_ty().unwrap(),
                    cursor.inst_debug(inst),
                    reaching_def,
                );

                cursor.replace_uses_with(val, closest_def);
                cursor.remove_inst_and_move_back();
            }
            Memory::Def(store) => {
                // this is pretty simple: we get whatever value we were storing,
                // mark that as the closest definition, and then remove the store.
                reaching_def
                    .get_mut(&store.pointer())
                    .unwrap()
                    .push(store.stored());

                cursor.remove_inst_and_move_back();
            }
        }
    }

    cursor.goto_last_inst(bb);
    let branch = cursor.current_inst().unwrap();
    let mut params = SmallVec::<[(usize, Value); 16]>::default();

    // if one of our successors has a φ node that came from an alloca we defined, rewrite
    // the branch to that successor to pass the most recent definition
    for successor in cfg.successors(bb) {
        params.insert_many(
            0,
            cursor.block_params(successor).iter().copied().enumerate(),
        );

        for (i, phi) in params.drain(..) {
            if let Some(&alloca) = phis.get(&phi) {
                let dbg = cursor.val_debug(phi);
                let reaching =
                    nearest_reaching_def(cursor, alloca, cursor.ty(phi), dbg, reaching_def);

                rewrite_pad_branch_argument(cursor, branch, successor, i, reaching);
            }
        }
    }

    // while we still have the most recent dominating reaching_defs in `reaching_def`,
    // we run renamer over the children.
    //
    // this ensures that they see the most recent definition when they encounter a load
    for child in domtree.children(bb) {
        cursor.goto_before(child);

        rename_variables_recursive(cursor, phis, reaching_def, cfg, domtree);
    }

    // once we've finished recursing, remove our defs from the stack so they don't
    // interfere with blocks that we don't actually dominate.
    for alloca in defs {
        let _ = reaching_def.get_mut(&alloca).unwrap().pop();
    }
}

fn rename_variables(
    cursor: &mut FuncCursor<'_>,
    allocas: &SaHashMap<Value, (Type, SmallVec<[Inst; 4]>)>,
    phis: &SaHashMap<Value, Value>,
    cfg: &ControlFlowGraph,
    domtree: &DominatorTree,
) {
    let mut reaching_def = SaHashMap::<Value, SmallVec<[Value; 4]>>::default();

    // initialize reaching_def, for every alloca we have no definition
    // at this point in the program yet.
    for &alloca in allocas.keys() {
        reaching_def.insert(alloca, smallvec![]);
    }

    cursor.goto_before(domtree.root());

    rename_variables_recursive(cursor, phis, &mut reaching_def, cfg, domtree);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::ControlFlowGraph;

    #[test]
    fn find_allocas_simple() {
        let mut module = Module::new("fig3.1");
        let sig = SigBuilder::new()
            .param(Type::i32())
            .param(Type::i32())
            .ret(Some(Type::i32()))
            .build();
        let f = module.declare_function("f", sig.clone());

        let mut b = module.define_function(
            "test",
            SigBuilder::new()
                .param(Type::bool())
                .ret(Some(Type::i32()))
                .build(),
        );

        let sig = b.import_signature(&sig);

        // fn i32 @f(i32, i32)
        //
        // fn i32 @test(bool) {
        // r(bool %0):
        //   %x = alloca i32
        //   %y = alloca i32
        //   %tmp = alloca i32
        //   %1 = undef i32
        //   store i32 %1, ptr %x
        //   store i32 %1, ptr %y
        //   store i32 %1, ptr %tmp
        //   br a
        //
        // a:
        //   condbr bool %0, b, c
        //
        // b:
        //   %2 = iconst i32 0
        //   store i32 %2, ptr %x
        //   store i32 %2, ptr %y
        //   br d
        //
        // c:
        //   %3 = load i32, ptr %x
        //   store i32 %3, ptr %tmp
        //   %4 = load i32, ptr %y
        //   store i32 %4, ptr %x
        //   %5 = load i32, ptr %tmp
        //   store i32 %5, ptr %y
        //   br d
        //
        // d:
        //   %6 = load i32, ptr %x
        //   %7 = load i32, ptr %y
        //   %8 = call i32 @f(i32 %6, i32 %7)
        //   store i32 %8, ptr %x
        //   condbr bool %0, a, e
        //
        // e:
        //   %9 = load i32, ptr %x
        //   ret i32 %9
        // }
        let bbr = b.create_block("r");
        let bba = b.create_block("a");
        let bbb = b.create_block("b");
        let bbc = b.create_block("c");
        let bbd = b.create_block("d");
        let bbe = b.create_block("e");

        let v0 = b.append_entry_params(bbr, DebugInfo::fake())[0];

        b.switch_to(bbr);
        let x = b.append().alloca(Type::i32(), DebugInfo::fake());
        let y = b.append().alloca(Type::i32(), DebugInfo::fake());
        let tmp = b.append().alloca(Type::i32(), DebugInfo::fake());
        let v1 = b.append().undef(Type::i32(), DebugInfo::fake());
        let x_def1 = b.append().store(v1, x, DebugInfo::fake());
        let y_def1 = b.append().store(v1, y, DebugInfo::fake());
        let tmp_def1 = b.append().store(v1, tmp, DebugInfo::fake());
        b.append().br(BlockWithParams::to(bba), DebugInfo::fake());

        b.switch_to(bba);
        b.append().condbr(
            v0,
            BlockWithParams::to(bbb),
            BlockWithParams::to(bbc),
            DebugInfo::fake(),
        );

        b.switch_to(bbb);
        let v2 = b.append().iconst(Type::i32(), 0, DebugInfo::fake());
        let x_def2 = b.append().store(v2, x, DebugInfo::fake());
        let y_def2 = b.append().store(v2, y, DebugInfo::fake());
        b.append().br(BlockWithParams::to(bbd), DebugInfo::fake());

        b.switch_to(bbc);
        let v3 = b.append().load(Type::i32(), x, DebugInfo::fake());
        let tmp_def2 = b.append().store(v3, tmp, DebugInfo::fake());
        let v4 = b.append().load(Type::i32(), y, DebugInfo::fake());
        let x_def3 = b.append().store(v4, x, DebugInfo::fake());
        let v5 = b.append().load(Type::i32(), tmp, DebugInfo::fake());
        let y_def3 = b.append().store(v5, y, DebugInfo::fake());
        b.append().br(BlockWithParams::to(bbd), DebugInfo::fake());

        b.switch_to(bbd);
        let v6 = b.append().load(Type::i32(), x, DebugInfo::fake());
        let v7 = b.append().load(Type::i32(), y, DebugInfo::fake());
        let v8 = b.append().call(f, sig, &[v6, v7], DebugInfo::fake());
        let v8 = b.inst_to_result(v8).unwrap();
        let x_def4 = b.append().store(v8, x, DebugInfo::fake());
        b.append().condbr(
            v0,
            BlockWithParams::to(bba),
            BlockWithParams::to(bbe),
            DebugInfo::fake(),
        );

        b.switch_to(bbe);
        let v9 = b.append().load(Type::i32(), x, DebugInfo::fake());
        b.append().ret_val(v9, DebugInfo::fake());

        let f = b.define();
        let func = module.function_mut(f);

        let cfg = ControlFlowGraph::compute(func);
        let domtree = DominatorTree::compute(func, &cfg);
        let allocas = find_promotable_allocas(&mut FuncCursor::over(func), &domtree);
        {
            let (ty, mut defs) = allocas[&x].clone();

            defs.sort();

            assert_eq!(ty, Type::i32());
            assert_eq!(defs.as_slice(), &[x_def1, x_def2, x_def3, x_def4]);
        }

        {
            let (ty, mut defs) = allocas[&y].clone();

            defs.sort();

            assert_eq!(ty, Type::i32());
            assert_eq!(defs.as_slice(), &[y_def1, y_def2, y_def3]);
        }

        {
            let (ty, mut defs) = allocas[&tmp].clone();

            defs.sort();

            assert_eq!(ty, Type::i32());
            assert_eq!(defs.as_slice(), &[tmp_def1, tmp_def2]);
        }
    }

    #[test]
    fn find_allocas_escaped() {
        let mut module = Module::new("fig3.1");
        let sig = SigBuilder::new().param(Type::ptr()).build();
        let f = module.declare_function("f", sig.clone());

        let mut b = module.define_function("test", SigBuilder::new().param(Type::ptr()).build());

        let sig = b.import_signature(&sig);

        let bb0 = b.create_block("r");
        let v0 = b.append_entry_params(bb0, DebugInfo::fake())[0];
        b.switch_to(bb0);
        let v1 = b.append().alloca(Type::ptr(), DebugInfo::fake());
        let v2 = b.append().alloca(Type::i8(), DebugInfo::fake());
        let v3 = b.append().alloca(Type::f32(), DebugInfo::fake());
        let v4 = b.append().alloca(Type::i64(), DebugInfo::fake());
        let ty = Type::array(&mut b.ctx().types_mut(), Type::bool(), 512);
        let v5 = b.append().alloca(ty, DebugInfo::fake());
        let v6 = b.append().alloca(Type::f64(), DebugInfo::fake());
        b.append().call(f, sig, &[v1], DebugInfo::fake());
        b.append().indirectcall(v0, sig, &[v3], DebugInfo::fake());
        b.append().ptoi(Type::i64(), v6, DebugInfo::fake());
        b.append().store(v4, v1, DebugInfo::fake());
        b.append().ret_void(DebugInfo::fake());

        let func = b.define();
        let func = module.function_mut(func);
        let cfg = ControlFlowGraph::compute(func);
        let domtree = DominatorTree::compute(func, &cfg);

        let allocas = find_promotable_allocas(&mut FuncCursor::over(func), &domtree);

        assert!(allocas.contains_key(&v2));
        assert!(allocas.contains_key(&v5));

        {
            let (alloca_ty, mut defs) = allocas[&v2].clone();

            defs.sort();

            assert_eq!(alloca_ty, Type::i8());
            assert_eq!(defs.as_slice(), &[]);
        }

        {
            let (alloca_ty, mut defs) = allocas[&v5].clone();

            defs.sort();

            assert_eq!(alloca_ty, ty);
            assert_eq!(defs.as_slice(), &[]);
        }
    }
}
