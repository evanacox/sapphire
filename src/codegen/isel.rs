//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaMap, SecondaryMap, SecondarySet};
use crate::codegen::*;
use crate::ir::{Block, Cursor, FuncView, Function, FunctionDefinition, Module, Value};
use crate::transforms::common::has_side_effect;
use crate::utility::{Packable, Str, StringPool};
use crate::{analysis, ir};
use std::collections::VecDeque;
use std::marker::PhantomData;

/// An instruction selector that lowers one [`Inst`] into (potentially many) [`MachInst`]s.
///
/// Specific implementations of this trait may be generic (e.g. working with multiple
/// potential [`ABI`] implementations), but for any selector it will produce code that
/// is ready to be register allocated.
///
/// [`Inst`]: ir::Inst
pub trait InstructionSelector<'module, 'target, Arch, Abi, Inst>: Sized
where
    Arch: Architecture,
    Abi: ABI<Arch, Inst>,
    Inst: MachInst<Arch>,
{
    /// Creates an instance of the selector with itself configured correctly.
    fn new() -> Self;

    /// Lowers a single SIR instruction into [`MachInst`]s for the specified
    /// architecture.
    ///
    /// This must report what it does to `ctx` in order for the isel pipeline to
    /// correctly lower a module. If any SIR instructions are merged when lowering the
    /// current instruction, this must be reported to `ctx` for correctness.
    fn lower(
        &mut self,
        inst: ir::Inst,
        def: &'module FunctionDefinition,
        frame: &mut <Abi as ABI<Arch, Inst>>::Frame,
        ctx: &mut LoweringContext<'module, 'target, Arch, Abi, Inst>,
    );
}

/// The context passed to any code doing instruction selection
pub type Ctx<'module, 'frame, 'target, 'ctx, Arch, Abi, Frame, Inst> = (
    &'module FunctionDefinition,
    &'frame mut Frame,
    &'ctx mut LoweringContext<'module, 'target, Arch, Abi, Inst>,
);

/// Context passed to instruction selection code that's actually a part of [`FunctionFrame`].
///
/// The frame is unnecessary here for one (since any code there would have `&self`) and would
/// actively prevent `&mut self` due to aliasing.
pub type FramelessCtx<'module, 'target, 'ctx, Arch, Abi, Inst> = (
    &'module FunctionDefinition,
    &'ctx mut LoweringContext<'module, 'target, Arch, Abi, Inst>,
);

// make linter not whine about complex types
type SilenceLinter<'module, 'target, Arch, Abi, Inst> = fn() -> (&'module Arch, &'target Abi, Inst);

/// The main instruction selection pipeline that takes in a target-specific
/// instruction selector and repeatedly invokes it to lower each instruction.
pub struct GenericISel<'module, 'target, Arch, Abi, Inst, Selector>
where
    Arch: Architecture + 'static,
    Abi: ABI<Arch, Inst> + 'static,
    Inst: MachInst<Arch> + 'static,
    Selector: InstructionSelector<'module, 'target, Arch, Abi, Inst> + 'static,
{
    selector: Selector,
    _unused: PhantomData<SilenceLinter<'module, 'target, Arch, Abi, Inst>>,
}

impl<'module, 'target, Arch, Abi, Inst, Selector>
    GenericISel<'module, 'target, Arch, Abi, Inst, Selector>
where
    Arch: Architecture + 'static,
    Abi: ABI<Arch, Inst> + 'static,
    Inst: MachInst<Arch> + 'static,
    Selector: InstructionSelector<'module, 'target, Arch, Abi, Inst> + 'static,
{
    /// Performs instruction selection over a SIR [`Module`] and emits
    /// a [`MIRModule`] that is ready for instruction scheduling and register allocation.
    ///
    /// The MIR emitted may use any number of virtual registers, but any physical registers
    /// used will be valid for the target and must be respected by the register allocator
    /// (as if instructions use specific physical registers it is required for correctness).
    pub fn lower(
        target: &'target mut Target<Arch, Abi, Inst>,
        module: &'module Module,
        options: CodegenOptions,
    ) -> MIRModule<Arch, Abi, Inst> {
        target.prepare_for(module);

        let mut isel = Self::new();
        let mut functions = Vec::default();
        let mut context = LoweringContext::new_for(target, module, options);

        for func in module.functions() {
            let f = module.function(func);

            if f.is_decl() {
                continue;
            }

            let mir = isel.emit_func(f, &mut context);

            functions.push(mir);
        }

        MIRModule::new(context.pool, Vec::default(), functions)
    }

    fn new() -> Self {
        Self {
            selector: Selector::new(),
            _unused: PhantomData::default(),
        }
    }

    fn perform_isel(
        &mut self,
        func: &'module Function,
        frame: &mut Abi::Frame,
        context: &mut LoweringContext<'module, 'target, Arch, Abi, Inst>,
        blocks: &ArenaMap<MIRBlock, MIRBlockInterval>,
    ) -> (Vec<MIRBlock>, SecondaryMap<MIRBlock, u32>) {
        let def = func.definition().unwrap();
        let mut cursor = FuncView::over(func);
        let mut block_length = SecondaryMap::<_, u32>::with_primary(blocks);
        let mut order = VecDeque::default();

        frame.compute_stack_layout(func, context);

        // we go backwards over the instructions, codegen-ing single instructions as needed
        // to determine which instructions are folded into others and which actually need to be generated
        //
        // we also track the length of each block, but not the interval. the interval will need to be updated later,
        // but we can only calculate the intervals once we know precisely how many instructions will be generated.
        // at this point, we know how long our block is but not where that block is relative to the beginning
        for block in analysis::compute_postorder(func) {
            cursor.goto_after(block);

            let mir_block = context.mir_block(block);
            let length = {
                let begin = context.current.len();

                // we need the begin/end linear lowering for some trickery with how the instruction
                // buffer is organized, we actually store two of them at once. see the documentation
                // of those two functions for more information
                while let Some(inst) = cursor.prev_inst() {
                    // we don't emit any instructions that have been merged, by definition
                    // if they get merged they only have one use and the computation
                    // is already shoved into another instruction
                    if !context.is_merged(inst) {
                        context.begin_linear_lowering();

                        // every instruction is lowered regardless of if it is used. any
                        // DCE should be done at the SIR level, not here.
                        self.selector.lower(inst, def, frame, context);

                        context.end_linear_lowering();
                    }
                }

                // the entry block's parameters are formal parameters, we need to get those from
                // physical registers and copy them to virtual registers for the rest of the codegen
                if cursor.is_entry_block(block) {
                    context.begin_linear_lowering();

                    // find the parameters that were actually used in the function body and
                    // get the ABI code to copy them into the correct spot
                    for &param in cursor.block_params(block).iter() {
                        if let Some(&reg) = context.vreg_constraints.get(param) {
                            frame.lower_parameter(
                                param,
                                WriteableReg::from_reg(reg),
                                (def, context),
                            );
                        }
                    }

                    context.end_linear_lowering();
                }

                context.current.len() - begin
            };

            block_length.insert(mir_block, length as u32);
            order.push_front(mir_block);
        }

        (Vec::from_iter(order.into_iter()), block_length)
    }

    fn emit_func(
        &mut self,
        func: &'module Function,
        context: &mut LoweringContext<'module, 'target, Arch, Abi, Inst>,
    ) -> (MIRFunction<Arch, Inst>, Abi::Frame) {
        let mut frame = {
            let view = FuncView::over(func);
            let entry = view
                .entry_block()
                .expect("function that isn't a decl must have an entry block");
            let params = view.block_params(entry);

            Abi::new_frame(func.signature(), params, func.compute_metadata().unwrap())
        };

        let (name, mut blocks) = context.prepare_for_func(func);
        let (order, block_length) = self.perform_isel(func, &mut frame, context, &blocks);

        // we haven't computed block lengths due to how isel works, need to do that now
        context.compute_block_lengths(&order, &block_length, &mut blocks);

        (
            MIRFunction::new(name, context.take_insts(), blocks, order),
            frame,
        )
    }
}

/// The "context" of a specific lowering.
///
/// This is given to a specific selector when its asked to lower an instruction,
/// this is all the information it needs to update when doing so.
pub struct LoweringContext<'module, 'target, Arch, Abi, Inst>
where
    Arch: Architecture,
    Abi: ABI<Arch, Inst>,
    Inst: MachInst<Arch>,
{
    /// The target that code is being generated for. This should be queried by the selector.
    pub target: &'target Target<Arch, Abi, Inst>,
    /// The module being lowered. This is here to refer to module-scoped information
    pub module: &'module Module,
    /// Codegen options, available for instruction selection code to access
    pub options: CodegenOptions,
    // this is the final buffer of instructions in program-order
    current: VecDeque<Inst>,
    // when lowering a single instruction, we push into this. when done with that instruction,
    // this is emptied and pushed into `current` in a way that preserves the program order
    current_linear: Vec<Inst>,
    pool: StringPool,
    // maps an ir::Block to its associated MIR block
    block_lookup: SecondaryMap<Block, MIRBlock>,
    // the set of all instructions that have exactly one use
    single_use: SecondarySet<ir::Inst>,
    // maps an instruction to the instruction it was merged with, if it was merged
    merged: SecondaryMap<ir::Inst, ir::Inst>,
    // maps an instruction to its "color," which is a way of modeling the sections of code
    // that are free of any side effects. any instructions that have the same color
    // are able to be merged with each-other safely
    colors: SecondaryMap<ir::Inst, u32>,
    // maps an ir::Value to the register it will be put into when it is emitted
    vreg_constraints: SecondaryMap<Value, Reg>,
    // the next integer vreg hardware number to give out
    next_int_vreg_id: usize,
    // the next float vreg hardware number to give out
    next_float_vreg_id: usize,
    // the current function being lowered
    func: Option<&'module Function>,
}

impl<'module, 'target, Arch, Abi, Inst> LoweringContext<'module, 'target, Arch, Abi, Inst>
where
    Arch: Architecture,
    Abi: ABI<Arch, Inst>,
    Inst: MachInst<Arch>,
{
    const CONSTANT_COLOR: u32 = !0;

    /// Creates a [`LoweringContext`] prepared for a specific target and module.
    pub fn new_for(
        target: &'target mut Target<Arch, Abi, Inst>,
        module: &'module Module,
        options: CodegenOptions,
    ) -> Self {
        Self {
            target,
            module,
            options,
            block_lookup: SecondaryMap::default(),
            pool: StringPool::default(),
            current: VecDeque::default(),
            current_linear: Vec::default(),
            single_use: SecondarySet::default(),
            merged: SecondaryMap::default(),
            colors: SecondaryMap::default(),
            vreg_constraints: SecondaryMap::default(),
            next_int_vreg_id: 0,
            next_float_vreg_id: 0,
            func: None,
        }
    }

    /// Prepares the [`LoweringContext`] to start having instructions from `func` be emitted.
    ///
    /// Returns the function name and block lookup, both suitable for giving to a [`MIRFunction`].
    ///
    /// This prepares the internal state for `func`, and computes things like usage data,
    /// instruction colors, and the block interval lookup.
    pub fn prepare_for_func(
        &mut self,
        func: &'module Function,
    ) -> (Str, ArenaMap<MIRBlock, MIRBlockInterval>) {
        self.func = Some(func);
        self.next_int_vreg_id = 0;
        self.next_float_vreg_id = 0;

        // fill out the internal data structures
        self.compute_uses();
        self.compute_colors();

        // return the function name and the new block lookup to our caller
        (self.pool.insert(func.name()), self.build_block_lookup())
    }

    /// Takes the current instruction buffer, emptying it in the process. The vec returned
    /// will be the contents of the function emitted so far, in program order.
    pub fn take_insts(&mut self) -> Vec<Inst> {
        let _ = self.current.make_contiguous();
        let mut result = Vec::with_capacity(self.current.len());

        {
            let (left, _) = self.current.as_slices();

            // make_contiguous should make the right one always empty, left will have everything.
            // this will turn into a `memcpy` since we have the capacity pre-allocated
            result.extend_from_slice(left);
        }

        self.current.clear();

        result
    }

    /// Push an instruction into the result buffer.
    ///
    /// This should be called in the order that the instructions should appear
    /// in program order, meaning that if you want `add` to be followed by a
    /// `mul` in the final program, you should call this with `add` and then
    /// call it again with `mul` after.
    #[inline]
    pub fn emit(&mut self, inst: Inst) {
        self.current_linear.push(inst);
    }

    /// Called before we begin lowering a single [`ir::Inst`]. This must be accompanied by
    /// a call to [`Self::end_linear_lowering`] after the lowering.
    ///
    /// This prepares the internal buffer so that the lowering code can emit
    /// [`MachInst`]s in program order while the [`ir::Inst`]s are being lowered
    /// in reverse order.
    pub fn begin_linear_lowering(&mut self) {
        // nothing to do here, for now
    }

    /// Finalizes the process began by [`Self::begin_linear_lowering`]. Inserts the instructions
    /// emitted by a single lowering into the MIR buffer.
    pub fn end_linear_lowering(&mut self) {
        // ex. consider the current state of the context:
        //   `current_linear` = [add, mul]
        //   `current` = [ret]
        //
        // we want `current` to be [add, mul, ret] after this, but we have to push to the front
        // so we iterate over linear in reverse.
        for inst in self.current_linear.drain(..).rev() {
            self.current.push_front(inst);
        }
    }

    /// Resolves (and possibly inserts) a string in the MIR module's
    /// string pool.
    #[inline]
    pub fn resolve(&mut self, string: &str) -> Str {
        self.pool.insert(string)
    }

    /// Finds the [`MIRBlock`] associated with a given [`Block`].
    #[inline]
    pub fn mir_block(&self, block: Block) -> MIRBlock {
        self.block_lookup[block]
    }

    /// Checks if the instruction `merge` can be merged with `base` during selection.
    ///
    /// Two instructions can only be merged if one of the following conditions
    /// are true AND the instruction only has one use in total:
    ///
    /// 1. The instruction to be merged is a constant of some sort
    /// 2. The instructions have the same side-effect 'color'
    #[inline]
    pub fn able_to_merge_with(&self, merge: ir::Inst, base: ir::Inst) -> bool {
        let merge_color = self.colors[merge];

        (merge_color == Self::CONSTANT_COLOR || merge_color == self.colors[base])
            && self.single_use.contains(merge)
    }

    /// Marks that the instruction `merge` was merged with `base`. This is only
    /// to be called when it has already been determined that the merge is safe.
    ///
    /// Once this is called, `merge` will not be lowered later.
    #[inline]
    pub fn mark_merged_with(&mut self, merge: ir::Inst, base: ir::Inst) {
        debug_assert!(self.single_use.contains(merge));
        debug_assert!(self.able_to_merge_with(merge, base));

        self.merged.insert(merge, base);
    }

    /// Marks the side-effect color of an instruction.
    ///
    /// An instruction's color is a way of distinguishing it from other
    /// instructions that are divided by side effects. Two instructions
    /// with the same color are guaranteed to not be in different blocks,
    /// and they are guaranteed to not have a side effect of any kind between them.
    #[inline]
    fn color_inst(&mut self, inst: ir::Inst, color: u32) {
        self.colors.insert(inst, color);
    }

    /// Marks an instruction as being a constant and thus 'immune' to merging
    /// restrictions.
    ///
    /// Constants will never be modified by side effects, we don't want to increase
    /// register pressure by pessimistically not merging them across color boundaries.
    #[inline]
    fn color_inst_constant(&mut self, constant: ir::Inst) {
        self.colors.insert(constant, Self::CONSTANT_COLOR);
    }

    /// Gets a new vreg for a given register class. This register is unique,
    /// it will not be returned again (and therefore must be kept if you want
    /// to use it multiple times).
    #[inline]
    pub fn next_vreg(&mut self, class: RegClass) -> Reg {
        let vreg = match class {
            RegClass::Int => {
                self.next_int_vreg_id += 1;

                VReg::int(self.next_int_vreg_id - 1)
            }
            RegClass::Float => {
                self.next_float_vreg_id += 1;

                VReg::int(self.next_float_vreg_id - 1)
            }
        };

        Reg::from_vreg(vreg)
    }

    /// Enforce a constraint that `value`s result be placed in `reg`. When
    /// the instruction yielding that value is emitted, the selector must
    /// follow this constraint.
    ///
    /// If a value does not have a constraint placed on it, it can be placed
    /// in any result (although any instruction without a side effect can also
    /// be skipped if its result is not constrained).
    ///
    /// The intent is that whenever a value is used, the instruction using it
    /// selects a register and constrains the value to be put in that register,
    /// and then once that instruction is emitted later it will be
    #[inline]
    pub fn constrain_result(&mut self, value: Value, reg: Reg) {
        self.vreg_constraints.insert(value, reg);
    }

    /// Gets a result register for a given value.
    ///
    /// If the value has a constraint placed on it, that register is returned.
    /// Otherwise, a new register is selected, the value is constrained to that
    /// register, and that register is returned.
    #[inline]
    pub fn result_reg(&mut self, value: Value, class: RegClass) -> Reg {
        match self.vreg_constraints.get(value) {
            Some(reg) => *reg,
            None => {
                let reg = self.next_vreg(class);

                self.constrain_result(value, reg);

                reg
            }
        }
    }

    /// If a value has a constrained result register, returns that. If it does not,
    /// this returns `None`.
    ///
    /// This is only here for instructions like `icmp` and `fcmp` that are not fully
    /// merged with branches, other instructions should not use this.
    #[inline]
    pub fn maybe_result_reg(&mut self, value: Value) -> Option<Reg> {
        self.vreg_constraints.get(value).copied()
    }

    /// Gets the current function being lowered.
    #[inline]
    pub fn func(&self) -> &'module Function {
        self.func.unwrap()
    }

    /// Checks if a given instruction has been merged with another or not
    #[inline]
    pub fn is_merged(&self, inst: ir::Inst) -> bool {
        self.merged.contains(inst)
    }

    // builds an arena mapping MIR blocks to their intervals in the resulting instruction buffer.
    // this function also maps SIR blocks to MIR blocks, so the selector can actually generate
    // valid jumps between blocks.
    //
    // for now these are invalid intervals, they will be filled in after the function has been
    // fully lowered.
    fn build_block_lookup(&mut self) -> ArenaMap<MIRBlock, MIRBlockInterval> {
        let mut blocks = ArenaMap::default();
        let mut view = FuncView::over(self.func());

        self.block_lookup = SecondaryMap::default();

        while let Some(block) = view.next_block() {
            // for now, every block is invalid. we just need temporary values to store
            let mir = MIRBlockInterval::reserved();
            let block_ref = blocks.insert(mir);

            self.block_lookup.insert(block, block_ref);
        }

        blocks
    }

    // computes 'colors' for instructions.
    //
    // two instructions with the same 'color' both share a "chunk" with another,
    // i.e. they both live in the same linear section of code that has no side effects
    // anywhere (except the first inst that may have changed the color). This means
    // they are safe to merge together in the instruction selector.
    //
    // the only instructions immune to this are constant materialization instructions,
    // they are always safe to merge by their nature. they are not considered to be "colored"
    // at all and are always safe to merge with another instruction.
    //
    // the same color will never span multiple basic blocks, as it's always possible that
    // one block is executed and another isn't. We don't want to do something weird like this:
    //
    // ```
    // .bb1:
    //    add r1, r2
    //
    // .bb2:
    //    mov r3, [r1 + r2]
    //
    // .bb3:
    //    mov [r4], r1
    // ```
    //
    // if the code spans multiple blocks, we are pessimistic and will not merge across
    // that boundary. Optimize it at the SIR level if it matters.
    fn compute_colors(&mut self) {
        let mut view = FuncView::over(self.func());
        let mut color = 0u32;

        self.colors = SecondaryMap::default();

        while view.next_block().is_some() {
            while let Some(inst) = view.next_inst() {
                // if the inst has any side effect, we immediately change color
                color += has_side_effect(view.dfg(), inst) as u32;

                if view.inst_data(inst).is_constant() {
                    self.color_inst_constant(inst);
                } else {
                    self.color_inst(inst, color);
                }
            }

            // each basic block changes our color
            color += 1;
        }
    }

    // finds all the instructions that are used exactly once, and are therefore able
    // to be merged into other instructions.
    fn compute_uses(&mut self) {
        let view = FuncView::over(self.func());
        let values = view.dfg().all_single_use_values();

        self.single_use.clear();

        for value in values {
            if let Some(inst) = view.dfg().value_to_inst(value) {
                if view.layout().is_inst_inserted(inst) {
                    self.single_use.insert(inst);
                }
            }
        }
    }

    fn compute_block_lengths(
        &self,
        order: &[MIRBlock],
        block_length: &SecondaryMap<MIRBlock, u32>,
        blocks: &mut ArenaMap<MIRBlock, MIRBlockInterval>,
    ) {
        // next step: we calculate the intervals by going over the blocks backwards
        let mut current = 0u32;

        // we know the very first block will start at 0 and is `len` long, so we
        // work our way down the list that way. we go block by block and compute
        // the beginning of each block based on the end of the previous
        for &block in order.iter() {
            let len = block_length[block];

            blocks[block] = MIRBlockInterval::from_indices(current, current + len);

            current += len;
        }

        debug_assert_eq!(current, self.current.len() as u32);
    }
}
