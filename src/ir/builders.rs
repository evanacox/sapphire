//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::*;
use crate::utility::{PackedOption, Str, TinyArray};
use smallvec::SmallVec;

/// Helper type for building a [`Signature`].
pub struct SigBuilder {
    vararg: bool,
    abi: CallConv,
    ret: PackedOption<Type>,
    params: SmallVec<[Type; 4]>,
}

impl SigBuilder {
    /// Creates a [`SigBuilder`] for the signature `void ()`
    pub fn new() -> Self {
        Self {
            vararg: false,
            abi: CallConv::C,
            ret: None.into(),
            params: SmallVec::default(),
        }
    }

    /// Marks the signature as having a variable number of arguments.
    pub fn vararg(self, value: bool) -> Self {
        Self {
            vararg: value,
            abi: self.abi,
            ret: self.ret,
            params: self.params,
        }
    }

    /// Marks the function as having a specified ABI.
    pub fn abi(self, abi: CallConv) -> Self {
        Self {
            vararg: self.vararg,
            abi,
            ret: self.ret,
            params: self.params,
        }
    }

    /// Marks the signature as having a given return type.
    pub fn ret(self, ret: Option<Type>) -> Self {
        Self {
            vararg: self.vararg,
            abi: self.abi,
            ret: ret.into(),
            params: self.params,
        }
    }

    /// Appends a parameter to the signature
    pub fn param(mut self, param: Type) -> Self {
        self.params.push(param);

        Self {
            vararg: self.vararg,
            abi: self.abi,
            ret: self.ret,
            params: self.params,
        }
    }

    /// Appends a list of parameters to the signature
    pub fn params(mut self, params: &[Type]) -> Self {
        self.params.extend_from_slice(params);

        Self {
            vararg: self.vararg,
            abi: self.abi,
            ret: self.ret,
            params: self.params,
        }
    }

    /// Builds the signature
    pub fn build(self) -> Signature {
        let ret = (self.ret.into(), RetAttributes::empty());
        let params = self
            .params
            .into_iter()
            .map(|p| (p, ParamAttributes::empty()))
            .collect();

        Signature::new(params, ret, self.abi, self.vararg)
    }
}

impl Default for SigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper type that appends to a function. Implements the [`InstBuilder`]
/// trait to allow easy instruction creation.
pub struct AppendBuilder<'b> {
    def: &'b mut FunctionDefinition,
    curr: Block,
}

impl<'b> InstBuilder<'b> for AppendBuilder<'b> {
    fn dfg(&self) -> &DataFlowGraph {
        &self.def.dfg
    }

    fn build(self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>) {
        let (inst, val) = self.def.dfg.create_inst(data, debug);

        self.def.layout.append_inst(inst, self.curr);

        (inst, val)
    }
}

/// Helper type for building a SIR function.
#[derive(Debug)]
pub struct FuncBuilder<'m> {
    module: &'m mut Module,
    func: Func,
    def: FunctionDefinition,
    current: Option<Block>,
}

impl<'m> FuncBuilder<'m> {
    pub(in crate::ir) fn new(module: &'m mut Module, func: Func) -> Self {
        Self {
            module,
            func,
            def: FunctionDefinition::default(),
            current: None,
        }
    }

    /// Finishes defining the function, and actually generates a full definition
    /// and inserts it into the module. Until this method is called, the function
    /// is not actually defined in the module.
    pub fn define(self) -> Func {
        self.module
            .function_mut(self.func)
            .replace_definition(self.def);

        self.func
    }

    /// Finds a block by its name, returning it if it's inserted into the current function.
    pub fn find_block(&mut self, name: &str) -> Option<Block> {
        let bb = match self.def.dfg.find_block(self.module.insert_string(name)) {
            Some(bb) => bb,
            None => return None,
        };

        self.def.layout.is_block_inserted(bb).then_some(bb)
    }

    /// Gets the name of a block that has been inserted into the function
    pub fn block_name(&self, block: Block) -> Str {
        debug_assert!(self.def.layout.is_block_inserted(block));

        self.def.dfg.block(block).name()
    }

    /// Gets the block parameters of a given block.
    pub fn block_params(&self, block: Block) -> &[Value] {
        debug_assert!(self.def.layout.is_block_inserted(block));

        self.def.dfg.block(block).params()
    }

    /// Creates a single basic block and returns it. This block is appended to
    /// the end of the block list.
    ///
    /// Note that this does not switch the builder to operate on that block,
    /// you still need to call [`Self::switch_to`].
    pub fn create_block(&mut self, name: &str) -> Block {
        let block = self.create_block_with_name(name);

        self.def.layout.append_block(block);

        block
    }

    /// Equivalent to [`Self::create_block`], except it inserts the block before `before`
    /// instead of appending it.
    pub fn create_block_before(&mut self, name: &str, before: Block) -> Block {
        let block = self.create_block_with_name(name);

        self.def.layout.insert_block_before(block, before);

        block
    }

    /// Equivalent to [`Self::create_block`], except it inserts the block after `after`
    /// instead of appending it.
    pub fn create_block_after(&mut self, name: &str, after: Block) -> Block {
        let block = self.create_block_with_name(name);

        self.def.layout.insert_block_after(block, after);

        block
    }

    /// Switches to inserting at a specific block.
    pub fn switch_to(&mut self, block: Block) {
        debug_assert!(self.def.layout.is_block_inserted(block));

        self.current = Some(block);
    }

    /// Adds a single block parameter of `ty` to `block` and returns a value
    /// that refers to it.
    pub fn append_block_param(&mut self, block: Block, ty: Type, debug: DebugInfo) -> Value {
        self.def.dfg.append_block_param(block, ty, debug)
    }

    /// Appends all the block parameters necessary for the parameters of the current function.
    /// This is meant to be used for creating a function's entry block, as the block parameters
    /// to the entry block get their value from the parameters.
    ///
    /// This is equivalent to calling [`Self::append_block_param`] once for each parameter
    /// type in the function signature.
    pub fn append_entry_params(&mut self, block: Block, debug: DebugInfo) -> TinyArray<Value, 2> {
        let tys: SmallVec<[Type; 2]> = self
            .function(self.func)
            .signature()
            .params()
            .iter()
            .map(|(ty, _)| *ty)
            .collect();

        let vals: SmallVec<[Value; 2]> = tys
            .into_iter()
            .map(|ty| self.append_block_param(block, ty, debug))
            .collect();

        TinyArray::from_small_vec(vals)
    }

    /// Gets the type of a value that was previously emitted by the builder.
    pub fn ty(&self, value: Value) -> Type {
        self.def.dfg.ty(value)
    }

    /// Returns a builder that can be used to append an instruction to
    /// the current block.
    ///
    /// If there is no current block, this will panic.
    pub fn append(&mut self) -> AppendBuilder<'_> {
        AppendBuilder {
            def: &mut self.def,
            curr: self.current.expect("cannot append without a current block"),
        }
    }

    /// Imports a signature into the function and returns a [`Sig`]
    /// that refers to it.
    ///
    /// This is intended to be used for calling other functions, where the
    /// signature needs to be known inside of the call instruction
    pub fn import_signature(&mut self, signature: &Signature) -> Sig {
        self.def.dfg.insert_sig(signature)
    }

    /// Resolves a [`Sig`] into a real signature. This signature must have been yielded
    /// at some point from [`Self::import_signature`].
    pub fn signature(&self, sig: Sig) -> &Signature {
        self.def.dfg.signature(sig)
    }

    /// Converts an [`Inst`] into a [`Value`] that refers to the result
    /// of the instruction if possible.
    ///
    /// Not all instructions actually yield results, those will return `None`
    pub fn inst_to_result(&self, inst: Inst) -> Option<Value> {
        self.def.dfg.inst_to_result(inst)
    }

    /// Gets the context associated with a given builder. This is
    /// the context that is owned by the module containing this function.
    pub fn ctx(&self) -> &ModuleContext {
        self.module.context()
    }

    /// Resolves a [`Func`] into a real function object.
    pub fn function(&self, func: Func) -> &Function {
        self.module.function(func)
    }

    /// Resolves a [`Func`] into a real function object.
    pub fn function_mut(&mut self, func: Func) -> &mut Function {
        self.module.function_mut(func)
    }

    /// Finds a [`Func`] with a given name. If the function has not been added to
    /// the module, `None` is returned.
    pub fn find_function_by_name(&self, func: &str) -> Option<Func> {
        self.module.find_function_by_name(func)
    }

    /// Checks if a given block is the entry block to the function
    pub fn is_entry_block(&self, block: Block) -> bool {
        self.def.layout.entry_block() == Some(block)
    }

    /// Gets the entry block of the function. Unless no blocks have been
    /// appended to the function, this will be `Some`.
    pub fn entry_block(&self) -> Option<Block> {
        self.def.layout.entry_block()
    }

    /// Gets a [`Func`] referring to the function being built.
    pub fn current_func(&self) -> Func {
        self.func
    }

    /// Gets the [`Signature`] of the function being built.
    pub fn current_signature(&self) -> &Signature {
        self.function(self.func).signature()
    }

    /// Returns the data-flow graph for the function
    pub fn dfg(&self) -> &DataFlowGraph {
        &self.def.dfg
    }

    /// Returns the data-flow graph for the function
    pub fn layout(&self) -> &Layout {
        &self.def.layout
    }

    fn create_block_with_name(&mut self, name: &str) -> Block {
        self.def.dfg.create_block(self.module.insert_string(name))
    }
}
