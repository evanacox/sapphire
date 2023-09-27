//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis;
use crate::ir::*;
use crate::reader2::{CompareOpcode, Lex, Opcode, TokPair, Token};
use crate::transforms;
use crate::utility::{Packable, SaHashMap, Str};
use smallvec::{smallvec, SmallVec};
use std::str::FromStr;
use std::{fmt, mem};

/// Parses SIR source code using the `reader2` parser.
pub fn parse_sir(name: &str, source: &str) -> Result<Module, String> {
    match Parser::new(name, source).parse() {
        Ok(module) => match transforms::verify_module(&module) {
            Ok(()) => Ok(module),
            Err(vec) => Err(super::format_verifier_error(name, source, vec)),
        },
        Err(e) => Err(super::format_parse_error(name, source, e)),
    }
}

/// A parser that parses a string containing Sapphire IR.
///
/// For performance reasons, this does very little in the way of validation, because
/// of this the public-facing parse functions all run a verify pass over the IR after
/// parsing.
pub struct Parser<'a> {
    lex: Lex<'a>,
    // the name of the source file, only used to store between `new` and `parse`
    name: String,
    // name_ref used for creating debug information
    name_ref: Str,
    // name of the local being parsed
    value_name: Option<Str>,
    // a lookup that maps a local register in a function to the value that it
    // refers to, this is populated in the order that blocks are parsed
    local_lookup: SaHashMap<&'a str, Value>,
    // a lookup that maps a stack slot name to the associated slot
    stack_lookup: SaHashMap<&'a str, StackSlot>,
    // a lookup that maps a block name to the associated block
    block_lookup: SaHashMap<&'a str, Block>,
    // the expected number for the next numbered instruction
    next_inst: usize,
    // a worklist for inserting terminators, this is necessary for referring to
    // blocks that may or may not actually exist yet
    terminator_worklist: Vec<(BranchWorklistFn<'a>, BranchWorklistContext<'a>)>,
    // the current token
    current: Option<TokPair<'a>>,
}

/// A typedef for a [`Result`] that has [`Error`] as the `Err` type
pub type ParseResult<'a, T> = Result<T, Error<'a>>;

type BranchPreprocessInfo<'a> = (TokPair<'a>, &'a str, SmallVec<[Value; 4]>);

type BranchWorklistFn<'a> =
    fn(&mut Parser<'a>, &mut FuncBuilder<'_>, BranchWorklistContext<'a>) -> ParseResult<'a, ()>;

struct BranchWorklistContext<'a> {
    dbg: DebugInfo,
    value: Value,
    block: Block,
    branches: SmallVec<[BranchPreprocessInfo<'a>; 2]>,
}

macro_rules! consume {
    ($self:expr, $p:pat, $ty:expr) => {{
        let next = $self.next($ty)?;

        if matches!(next.tok, $p) {
            next
        } else {
            return Err(Error::unexpected(next, concat!($ty)));
        }
    }};
}

macro_rules! needed_comma_previously {
    ($comma_count:expr, $pair:expr) => {{
        if $comma_count < 0 {
            return Err(Error::unexpected($pair, "','"));
        }

        $comma_count -= 1;
    }};
}

macro_rules! got_closing_symbol {
    ($comma_count:expr, $pair:expr, $expected:expr) => {{
        if $comma_count > 0 {
            return Err(Error::unexpected($pair, $expected));
        }

        break;
    }};
}

macro_rules! got_comma {
    ($comma_count:expr, $pair:expr, $expected:expr) => {{
        if $comma_count >= 0 {
            return Err(Error::err(
                $pair,
                format!("expected '{}' but got duplicate comma", $expected),
            ));
        }

        $comma_count += 1;
    }};
}

impl<'a> Parser<'a> {
    /// Creates a parser for a [`Module`] based on a file named `name`.
    ///
    /// `source` will be parsed into the module when [`Self::parse`] is called.
    pub fn new(name: &str, source: &'a str) -> Self {
        Self {
            lex: Lex::new(source),
            name: name.to_string(),
            name_ref: Str::reserved(),
            value_name: None,
            local_lookup: SaHashMap::default(),
            stack_lookup: SaHashMap::default(),
            block_lookup: SaHashMap::default(),
            next_inst: 0,
            terminator_worklist: Vec::default(),
            current: None,
        }
    }

    /// Parses the file, and if there are no errors returns a [`Module`]
    pub fn parse(mut self) -> ParseResult<'a, Module> {
        let mut module = Module::new(&self.name);

        // the context is a Arc<T> reference, we keep a copy so
        // that we don't have issues with the borrow checker
        let ctx = module.context().clone();
        self.name_ref = module.name();

        //
        // basic idea: we make an initial pass over the tokens,
        // declaring every function in the module and computing RPO
        // for the blocks of every function.
        //
        // we also keep all the tokens in each block categorized by block.
        //
        // once we've done this for every function, we can begin building the module
        // in reverse-postorder, allowing us to parse stuff where people use SSA values
        // "before" (file-wise not CFG-wise) they are defined
        while !self.lex.is_at_end() {
            let next = self.next("fn or global").expect("already checked for end");

            match next.tok {
                Token::Fn => {
                    self.local_lookup.clear();

                    let _ = self.parse_func(&mut module, &ctx)?;
                }
                _ => return Err(Error::message(next, "expected 'fn' or EOF")),
            }
        }

        Ok(module)
    }

    // parses a function declaration or definition, depending on which is present
    fn parse_func(&mut self, module: &mut Module, ctx: &ModuleContext) -> ParseResult<'a, Func> {
        let return_ty = self.parse_return_ty(ctx)?;
        let name = self.parse_global_ident()?;
        let signature = self.parse_rest_of_sig(return_ty, ctx)?;
        let func = module.declare_function(name, signature);

        self.local_lookup.clear();
        self.stack_lookup.clear();
        self.block_lookup.clear();
        self.next_inst = 0;

        if self
            .lex
            .peek_token()
            .is_some_and(|pair| matches!(pair.tok, Token::CurlyOpen))
        {
            let mut b = module.define_existing_function(func);

            consume!(self, Token::CurlyOpen, "{");

            while self
                .lex
                .peek_token()
                .is_some_and(|pair| matches!(pair.tok, Token::StackIdent(_)))
            {
                let name = self.parse_stack_ident()?;

                consume!(self, Token::Eq, "=");
                consume!(self, Token::Stack, "stack");

                let ty = self.parse_ty(ctx)?;
                let slot = b.create_stack_slot(name, ty);

                self.stack_lookup.insert(name, slot);
            }

            while !self.lex.is_at_end() {
                match self
                    .lex
                    .peek_token()
                    .expect("already checked, not at end")
                    .tok
                {
                    Token::CurlyClose => break,
                    _ => {
                        self.parse_block(&mut b, ctx)?;
                    }
                }
            }

            consume!(self, Token::CurlyClose, "}");

            for (item, context) in mem::take(&mut self.terminator_worklist) {
                item(self, &mut b, context)?;
            }

            b.define();
        }

        Ok(func)
    }

    // parses a function return type, returns Ok(None) for void
    //
    // return types take the form `("noalias" | "nonnull")* ("void" | ty)`,
    // i.e. a list of attributes and then `void` or a type.
    fn parse_return_ty(
        &mut self,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Option<(Type, RetAttributes)>> {
        let mut attributes = RetAttributes::NONE;

        loop {
            let next = self.next("return type")?;

            // we keep looping until we hit a type, void, EOF, or something
            // that can't be parsed as a type. this will always terminate in one way
            // or another if the lexer is working correctly
            match next.tok {
                Token::NoAlias => attributes |= RetAttributes::NOALIAS,
                Token::NonNull => attributes |= RetAttributes::NONNULL,
                Token::Void => {
                    return if attributes != RetAttributes::NONE {
                        Err(Error::message(
                            next,
                            "cannot have attributes on 'void' return type",
                        ))
                    } else {
                        Ok(None)
                    }
                }
                _ => {
                    let ty = self.parse_ty_at_current(next, ctx)?;

                    return if attributes != RetAttributes::NONE && ty != Type::ptr() {
                        Err(Error::message(
                            next,
                            "cannot have return attributes on non-'ptr' return type",
                        ))
                    } else {
                        return Ok(Some((ty, attributes)));
                    };
                }
            }
        }
    }

    // parses the parameter list and (possible) ABI tag, returning a complete function signature
    //
    // roughly parses this: "(T1, T2, T3, ...) <abi>"
    fn parse_rest_of_sig(&mut self, ret: RetTy, ctx: &ModuleContext) -> ParseResult<'a, Signature> {
        let mut variadic = false;
        let mut builder = SigBuilder::default();
        let mut comma_count = 0;
        consume!(self, Token::ParenOpen, "(");

        // parse the parameter list while ensuring `...` is at the end AND
        // that our commas are correct the entire way through
        while !self.lex.is_at_end() {
            let next = self
                .next("type, '...' or ')'")
                .expect("already checked for end");

            match next.tok {
                Token::Variadic => {
                    needed_comma_previously!(comma_count, next);

                    variadic = true;
                }
                Token::ParenClose => got_closing_symbol!(comma_count, next, "type or '...'"),
                Token::Comma => got_comma!(comma_count, next, "type, '...' or ')'"),
                _ => {
                    needed_comma_previously!(comma_count, next);

                    let (ty, attributes) = self.parse_parameter_at_current(next, ctx)?;

                    if variadic {
                        return Err(Error::message(next, "'...' must be at end of signature"));
                    }

                    builder = builder.param_with_attribute(ty, attributes);
                }
            }
        }

        // already consumed ) if we got out of the loop.
        //
        // now we check if there's an abi that the function specified, there might not be
        if let Some(maybe_abi) = self.lex.peek_token() {
            let abi = match maybe_abi.tok {
                Token::CCC => Some(CallConv::C),
                Token::SysV => Some(CallConv::SysV),
                Token::Win64 => Some(CallConv::Win64),
                _ => None,
            };

            if let Some(cc) = abi {
                self.next("calling convention")?;

                builder = builder.abi(cc);
            }
        }

        Ok(builder.ret_with_attribute(ret).vararg(variadic).build())
    }

    fn parse_parameter_at_current(
        &mut self,
        mut pair: TokPair<'a>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, (Type, ParamAttributes)> {
        let mut attributes = ParamAttributes::NONE;

        loop {
            // we keep looping until we hit a type, EOF, or something
            // that can't be parsed as a type.
            match pair.tok {
                Token::NoAlias => attributes |= ParamAttributes::NOALIAS,
                Token::NonNull => attributes |= ParamAttributes::NONNULL,
                Token::ByVal => {
                    consume!(self, Token::ParenOpen, "(");
                    let val = self.parse_int_literal(64)?;
                    consume!(self, Token::ParenClose, ")");

                    attributes |= ParamAttributes::byval(val as usize);
                }
                _ => {
                    let ty = self.parse_ty_at_current(pair, ctx)?;

                    return if attributes != ParamAttributes::NONE && ty != Type::ptr() {
                        Err(Error::message(
                            pair,
                            "cannot have param attributes on non-'ptr' parameter",
                        ))
                    } else {
                        Ok((ty, attributes))
                    };
                }
            }

            pair = self.next("parameter attributes or type")?;
        }
    }

    fn parse_block(&mut self, b: &mut FuncBuilder<'_>, ctx: &ModuleContext) -> ParseResult<'a, ()> {
        let (name, bb) = self.parse_block_header(b, ctx)?;

        b.switch_to(bb);
        self.parse_block_body(b, ctx, bb)?;

        self.block_lookup.insert(name, bb);

        Ok(())
    }

    fn parse_block_header(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, (&'a str, Block)> {
        let mut comma_count = 0;
        let name = self.parse_label_ident()?;
        let func = b.current_func();
        let bb = b.create_block(name);
        let maybe_param_list = self.next("':' or '('")?;

        // block parameter list is completely optional, check if we have it first
        match maybe_param_list.tok {
            Token::Colon => {}
            Token::ParenOpen => {
                // parse block parameters, add them to the block, and add them as variables in
                // the local lookup so that we can actually see them later
                loop {
                    let next = self.next("type or ')'").expect("already checked for end");

                    match next.tok {
                        Token::ParenClose => got_closing_symbol!(comma_count, next, "type"),
                        Token::Comma => got_comma!(comma_count, next, "type or ')'"),
                        _ => {
                            needed_comma_previously!(comma_count, next);

                            let ty = self.parse_ty_at_current(next, ctx)?;
                            let name = self.parse_new_local_ident(ctx)?;
                            let pair = self.current.unwrap();
                            let val = b.append_block_param(bb, ty, self.debug());

                            self.insert_new_value(pair, name, val)?;
                        }
                    }
                }

                consume!(self, Token::Colon, ":");
            }
            _ => return Err(Error::unexpected(maybe_param_list, "':' or '('")),
        }

        Ok((name, bb))
    }

    // parses instructions and builds up a basic block
    fn parse_block_body(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        bb: Block,
    ) -> ParseResult<'a, ()> {
        // consume instructions while there are any
        while !self.parse_instruction(b, ctx)? {
            //
        }

        // if the next is not either a block ident or a }, there are instructions
        // after a terminator and we need to error out
        let peeked = self
            .lex
            .peek_token()
            .ok_or_else(|| Error::missing("expected a '}' or block name"))?;

        match peeked.tok {
            Token::LabelIdent(_) | Token::CurlyClose => Ok(()),
            _ if Self::parse_peeked_label_ident(peeked).is_ok() => Ok(()),
            _ => Err(Error::unexpected(peeked, "'}' or block name")),
        }
    }

    // parses a single instruction, returning whether or not it was a terminator
    fn parse_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, bool> {
        let next = self
            .lex
            .peek_token()
            .ok_or_else(|| Error::missing("expected instruction or '}'"))?;

        match next.tok {
            Token::LocalIdent(_) => {
                let name = self.parse_new_local_ident(ctx)?;

                consume!(self, Token::Eq, "=");

                let val = self.parse_val_yielding_instruction(b, ctx)?;

                self.insert_new_value(next, name, val)?;

                Ok(false)
            }
            _ => {
                let next = self.next("opcode")?;

                self.parse_void_instruction(b, ctx, next)
            }
        }
    }

    // parses an instruction that yields a value, returning the value
    fn parse_val_yielding_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let inst = self.next("instruction opcode")?;
        let Token::Opcode(opcode) = inst.tok else {
            return Err(Error::unexpected(inst, "instruction opcode"));
        };

        match opcode {
            Opcode::Call => match self.parse_call_instruction(b, ctx)? {
                Some(val) => Ok(val),
                None => Err(Error::message(
                    inst,
                    "unable to bind 'call' returning 'void' to a result",
                )),
            },
            Opcode::IndirectCall => match self.parse_indirect_call_instruction(b, ctx)? {
                Some(val) => Ok(val),
                None => Err(Error::message(
                    inst,
                    "unable to bind 'indirectcall' returning 'void' to a result",
                )),
            },
            Opcode::FCmp | Opcode::ICmp => self.parse_cmp_instruction(b, ctx, opcode),
            Opcode::Sel => self.parse_sel_instruction(b, ctx),
            Opcode::Br | Opcode::CondBr | Opcode::Unreachable | Opcode::Ret => Err(Error::message(
                inst,
                "cannot bind terminator instruction to result",
            )),
            Opcode::And
            | Opcode::Or
            | Opcode::Xor
            | Opcode::Shl
            | Opcode::AShr
            | Opcode::LShr
            | Opcode::IAdd
            | Opcode::ISub
            | Opcode::IMul
            | Opcode::SDiv
            | Opcode::UDiv
            | Opcode::SRem
            | Opcode::URem
            | Opcode::FNeg
            | Opcode::FAdd
            | Opcode::FSub
            | Opcode::FMul
            | Opcode::FDiv
            | Opcode::FRem => self.parse_arith_instruction(b, ctx, opcode),
            Opcode::Alloca => self.parse_alloca_instruction(b, ctx),
            Opcode::Load => self.parse_load_instruction(b, ctx),
            Opcode::Store => Err(Error::unexpected(
                inst,
                "cannot bind 'store' instruction to result",
            )),
            Opcode::Offset => self.parse_offset_instruction(b, ctx),
            Opcode::Extract => self.parse_extract_instruction(b, ctx),
            Opcode::Insert => self.parse_insert_instruction(b, ctx),
            Opcode::ElemPtr => self.parse_elemptr_instruction(b, ctx),
            Opcode::Sext | Opcode::Zext | Opcode::Trunc => {
                self.parse_int_to_int_instruction(b, ctx, opcode)
            }
            Opcode::IToB => self.parse_itob_instruction(b, ctx),
            Opcode::BToI => self.parse_btoi_instruction(b, ctx),
            Opcode::SIToF | Opcode::UIToF => self.parse_int_to_float_instruction(b, ctx, opcode),
            Opcode::FToSI | Opcode::FToUI => self.parse_float_to_int_instruction(b, ctx, opcode),
            Opcode::FExt | Opcode::FTrunc => self.parse_float_to_float_instruction(b, ctx, opcode),
            Opcode::IToP => self.parse_itop_instruction(b, ctx),
            Opcode::PToI => self.parse_ptoi_instruction(b, ctx),
            Opcode::IConst => self.parse_iconst_instruction(b, ctx),
            Opcode::FConst => self.parse_fconst_instruction(b, ctx),
            Opcode::BConst => self.parse_bconst_instruction(b, ctx),
            Opcode::Null => self.parse_null_instruction(b, ctx),
            Opcode::Undef => self.parse_undef_instruction(b, ctx),
            Opcode::StackSlot => self.parse_stack_slot_instruction(b, ctx),
            Opcode::GlobalAddr => self.parse_global_addr_instruction(b, ctx),
        }
    }

    // parses an instruction without a result, returning whether it was a terminator or not
    fn parse_void_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        curr: TokPair<'a>,
    ) -> ParseResult<'a, bool> {
        let opc = match curr.tok {
            Token::Opcode(opc) => opc,
            _ => return Err(Error::unexpected(curr, "instruction opcode")),
        };

        match opc {
            Opcode::Br => {
                self.parse_br_instruction(b, ctx)?;

                Ok(true)
            }
            Opcode::CondBr => {
                self.parse_cond_br_instruction(b, ctx)?;

                Ok(true)
            }
            Opcode::Unreachable => {
                self.parse_unreachable_instruction(b)?;

                Ok(true)
            }
            Opcode::Ret => {
                self.parse_ret_instruction(b, ctx)?;

                Ok(true)
            }
            Opcode::Call => match self.parse_call_instruction(b, ctx)? {
                Some(result) => Err(Error::message(
                    curr,
                    "call cannot return a value without being bound to a name",
                )),
                None => Ok(false),
            },
            Opcode::IndirectCall => match self.parse_indirect_call_instruction(b, ctx)? {
                Some(result) => Err(Error::message(
                    curr,
                    "indirect cannot return a value without being bound to a name",
                )),
                None => Ok(false),
            },
            Opcode::Store => {
                self.parse_store_instruction(b, ctx)?;

                Ok(false)
            }
            _ => Err(Error::message(
                curr,
                "instruction with result must be bound to a name",
            )),
        }
    }

    fn br_instruction_worklist(
        &mut self,
        b: &mut FuncBuilder<'_>,
        mut context: BranchWorklistContext<'a>,
    ) -> ParseResult<'a, ()> {
        b.switch_to(context.block);

        let target = context.branches.remove(0);
        let target = self.finish_parse_branch_target(target)?;

        b.append().br(target, context.dbg);

        Ok(())
    }

    // parses a branch instruction
    fn parse_br_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, ()> {
        let dbg = self.debug();
        let target = self.preprocess_branch_target(b, ctx)?;

        let context = BranchWorklistContext {
            dbg,
            value: Value::reserved(),
            block: b.current_block(),
            branches: smallvec![target],
        };

        self.terminator_worklist
            .push((Self::br_instruction_worklist, context));

        Ok(())
    }

    fn cond_br_instruction_worklist(
        &mut self,
        b: &mut FuncBuilder<'_>,
        mut context: BranchWorklistContext<'a>,
    ) -> ParseResult<'a, ()> {
        b.switch_to(context.block);

        let if_false = context.branches.pop().unwrap();
        let if_false = self.finish_parse_branch_target(if_false)?;

        let if_true = context.branches.pop().unwrap();
        let if_true = self.finish_parse_branch_target(if_true)?;

        b.append()
            .condbr(context.value, if_true, if_false, context.dbg);

        Ok(())
    }

    // parses a conditional branch instruction
    fn parse_cond_br_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, ()> {
        let dbg = self.debug();
        consume!(self, Token::Bool, "bool");
        let cond = self.parse_existing_value(b, ctx, Type::bool())?;
        consume!(self, Token::Comma, ",");
        let if_true = self.preprocess_branch_target(b, ctx)?;
        consume!(self, Token::Comma, ",");
        let if_false = self.preprocess_branch_target(b, ctx)?;

        let context = BranchWorklistContext {
            dbg,
            block: b.current_block(),
            value: cond,
            branches: smallvec![if_true, if_false],
        };

        self.terminator_worklist
            .push((Self::cond_br_instruction_worklist, context));

        Ok(())
    }

    // parses an `unreachable` instruction
    fn parse_unreachable_instruction(&mut self, b: &mut FuncBuilder<'_>) -> ParseResult<'a, ()> {
        let _ = b.append().unreachable(self.debug());

        Ok(())
    }

    // parses an `unreachable` instruction
    fn parse_ret_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, ()> {
        let dbg = self.debug();
        let next = self.next("void or type")?;

        if matches!(next.tok, Token::Void) {
            b.append().ret_void(dbg);
        } else {
            let ty = self.parse_ty_at_current(next, ctx)?;
            let val = self.parse_existing_value(b, ctx, ty)?;

            b.append().ret_val(val, dbg);
        }

        Ok(())
    }

    // preprocesses a block target from a branch with an optional param list, e.g. `bb0(i32 %1)
    fn preprocess_branch_target(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, BranchPreprocessInfo<'a>> {
        let name = self.parse_label_ident()?;
        let tok = self.current.unwrap();

        if self
            .lex
            .peek_token()
            .is_some_and(|pair| matches!(pair.tok, Token::ParenOpen))
        {
            consume!(self, Token::ParenOpen, "(");

            let args = self.parse_call_args(b, ctx)?;

            if args.is_empty() {
                Err(Error::message(
                    self.current.unwrap(),
                    "cannot use '()'s with an empty block parameter list",
                ))
            } else {
                Ok((tok, name, args))
            }
        } else {
            Ok((tok, name, SmallVec::default()))
        }
    }

    // turns the preprocessed branch target info into a real target
    fn finish_parse_branch_target(
        &mut self,
        (tok, name, args): BranchPreprocessInfo<'a>,
    ) -> ParseResult<'a, BlockWithParams> {
        let bb = match self.block_lookup.get(name) {
            Some(block) => *block,
            None => return Err(Error::err(tok, format!("unknown block name '{name}'"))),
        };

        if args.is_empty() {
            Ok(BlockWithParams::to(bb))
        } else {
            Ok(BlockWithParams::new(bb, &args))
        }
    }

    // parses an indirect call instruction, e.g. `indirectcall i32 (ptr, ...) %0(ptr %1, i32 %2)
    fn parse_indirect_call_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Option<Value>> {
        let dbg = self.debug();
        let return_ty = self.parse_return_ty(ctx)?;
        let sig = self.parse_rest_of_sig(return_ty, ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Ptr, "ptr");
        let callee = self.parse_existing_value(b, ctx, Type::ptr())?;

        // parse_call_args assumes the ( is consumed
        consume!(self, Token::ParenOpen, "(");
        let args = self.parse_call_args(b, ctx)?;

        let sig = b.import_signature(&sig);
        let inst = b.append().indirectcall(callee, sig, &args, dbg);

        Ok(b.dfg().inst_to_result(inst))
    }

    // parses a call instruction, e.g. `call i32 @printf(ptr %0, i32 %1)
    fn parse_call_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Option<Value>> {
        let dbg = self.debug();
        let return_ty = self.parse_return_ty(ctx)?;
        let callee = match b.find_function_by_name(self.parse_global_ident()?) {
            Some(func) => func,
            None => {
                return Err(Error::message(
                    self.current.unwrap(),
                    "function not found, must be declared before usage",
                ));
            }
        };

        let sig = b.function(callee).signature().clone();

        // parse_call_args assumes the ( is consumed
        consume!(self, Token::ParenOpen, "(");
        let args = self.parse_call_args(b, ctx)?;
        let sig = b.import_signature(&sig);
        let inst = b.append().call(callee, sig, &args, dbg);

        Ok(b.dfg().inst_to_result(inst))
    }

    // parses arguments to a call or branch target, including the `)`.
    //
    // NOTE: does not consume the opening `(` for ease of use with terminators,
    // where the '(' is omitted for 0 argument targets.
    fn parse_call_args(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, SmallVec<[Value; 4]>> {
        let mut comma_count = 0;
        let mut values = SmallVec::default();

        loop {
            let next = self.next("type or ')'").expect("already checked for end");

            match next.tok {
                Token::ParenClose => got_closing_symbol!(comma_count, next, "type"),
                Token::Comma => got_comma!(comma_count, next, "type or ')'"),
                _ => {
                    needed_comma_previously!(comma_count, next);

                    let (_, val) = self.parse_ty_val_at_current(b, ctx, next)?;

                    values.push(val);
                }
            }
        }

        Ok(values)
    }

    // parses an icmp or fcmp instruction
    fn parse_cmp_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        opcode: Opcode,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let icmp = matches!(opcode, Opcode::ICmp);
        let cmp_opc = consume!(self, Token::CmpOpcode(_), "icmp or fcmp comparison");
        let Token::CmpOpcode(opc) = cmp_opc.tok else {
            unreachable!()
        };

        if icmp {
            let comparison = match opc {
                CompareOpcode::Eq => ICmpOp::EQ,
                CompareOpcode::Ne => ICmpOp::NE,
                CompareOpcode::Ugt => ICmpOp::UGT,
                CompareOpcode::Ult => ICmpOp::ULT,
                CompareOpcode::Uge => ICmpOp::UGE,
                CompareOpcode::Ule => ICmpOp::ULE,
                CompareOpcode::Sgt => ICmpOp::SGT,
                CompareOpcode::Slt => ICmpOp::SLT,
                CompareOpcode::Sge => ICmpOp::SGE,
                CompareOpcode::Sle => ICmpOp::SLE,
                _ => return Err(Error::unexpected(cmp_opc, "icmp comparison")),
            };

            let ty = self.parse_ptr_bool_or_int_ty(ctx)?;
            let (lhs, rhs) = self.parse_binop_lhs_rhs(b, ctx, ty)?;

            Ok(b.append().icmp(comparison, lhs, rhs, dbg))
        } else {
            let comparison = match opc {
                CompareOpcode::Ugt => FCmpOp::UGT,
                CompareOpcode::Ult => FCmpOp::ULT,
                CompareOpcode::Uge => FCmpOp::UGE,
                CompareOpcode::Ule => FCmpOp::ULE,
                CompareOpcode::Ord => FCmpOp::ORD,
                CompareOpcode::Uno => FCmpOp::UNO,
                CompareOpcode::Ueq => FCmpOp::UEQ,
                CompareOpcode::Une => FCmpOp::UNE,
                CompareOpcode::Oeq => FCmpOp::OEQ,
                CompareOpcode::One => FCmpOp::ONE,
                CompareOpcode::Ogt => FCmpOp::OGT,
                CompareOpcode::Olt => FCmpOp::OLT,
                CompareOpcode::Oge => FCmpOp::OGE,
                CompareOpcode::Ole => FCmpOp::OLE,
                _ => return Err(Error::unexpected(cmp_opc, "fcmp comparison")),
            };

            let ty = self.parse_float_ty(ctx)?;
            let (lhs, rhs) = self.parse_binop_lhs_rhs(b, ctx, ty)?;

            Ok(b.append().fcmp(comparison, lhs, rhs, dbg))
        }
    }

    // parses a sel instruction, e.g. sel bool %0, i32 %1, i32 %2
    fn parse_sel_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let curr = self.current.unwrap();
        let dbg = self.debug();
        let ty = self.parse_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Bool, "bool");
        let cond = self.parse_existing_value(b, ctx, Type::bool())?;
        consume!(self, Token::Comma, ",");
        let if_true = self.parse_existing_value(b, ctx, ty)?;
        consume!(self, Token::Comma, ",");
        let if_false = self.parse_existing_value(b, ctx, ty)?;

        Ok(b.append().sel(cond, if_true, if_false, dbg))
    }

    // parses an arithmetic instruction (bitwise, and integral/float arithmetic)
    fn parse_arith_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        opcode: Opcode,
    ) -> ParseResult<'a, Value> {
        macro_rules! parse_binary_arith {
            ($self:expr, $b:expr, $ctx:expr, $name:ident, $ty_guard:ident) => {{
                let dbg = self.debug();
                let ty = $self.$ty_guard($ctx)?;
                let (lhs, rhs) = $self.parse_binop_lhs_rhs($b, $ctx, ty)?;

                Ok($b.append().$name(lhs, rhs, dbg))
            }};
        }

        macro_rules! parse_bitwise_arith {
            ($self:expr, $b:expr, $ctx:expr, $name:ident) => {{
                parse_binary_arith!($self, $b, $ctx, $name, parse_int_or_bool_ty)
            }};
        }

        macro_rules! parse_integral_arith {
            ($self:expr, $b:expr, $ctx:expr, $name:ident) => {{
                parse_binary_arith!($self, $b, $ctx, $name, parse_int_ty)
            }};
        }

        macro_rules! parse_float_arith {
            ($self:expr, $b:expr, $ctx:expr, $name:ident) => {{
                parse_binary_arith!($self, $b, $ctx, $name, parse_float_ty)
            }};
        }

        match opcode {
            Opcode::And => parse_bitwise_arith!(self, b, ctx, and),
            Opcode::Or => parse_bitwise_arith!(self, b, ctx, or),
            Opcode::Xor => parse_bitwise_arith!(self, b, ctx, xor),
            Opcode::Shl => parse_bitwise_arith!(self, b, ctx, shl),
            Opcode::AShr => parse_bitwise_arith!(self, b, ctx, ashr),
            Opcode::LShr => parse_bitwise_arith!(self, b, ctx, lshr),
            Opcode::IAdd => parse_integral_arith!(self, b, ctx, iadd),
            Opcode::ISub => parse_integral_arith!(self, b, ctx, isub),
            Opcode::IMul => parse_integral_arith!(self, b, ctx, imul),
            Opcode::SDiv => parse_integral_arith!(self, b, ctx, sdiv),
            Opcode::UDiv => parse_integral_arith!(self, b, ctx, udiv),
            Opcode::SRem => parse_integral_arith!(self, b, ctx, srem),
            Opcode::URem => parse_integral_arith!(self, b, ctx, urem),
            Opcode::FNeg => {
                let ty = self.parse_float_ty(ctx)?;
                let val = self.parse_existing_value(b, ctx, ty)?;

                Ok(b.append().fneg(val, self.debug()))
            }
            Opcode::FAdd => parse_float_arith!(self, b, ctx, fadd),
            Opcode::FSub => parse_float_arith!(self, b, ctx, fsub),
            Opcode::FMul => parse_float_arith!(self, b, ctx, fmul),
            Opcode::FDiv => parse_float_arith!(self, b, ctx, fdiv),
            Opcode::FRem => parse_float_arith!(self, b, ctx, frem),
            _ => unreachable!(),
        }
    }

    fn parse_alloca_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_ty(ctx)?;

        Ok(b.append().alloca(ty, dbg))
    }

    fn parse_load_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let next = self
            .lex
            .peek_token()
            .ok_or(Error::missing("expected volatile or type"))?;
        let volatile = if matches!(next.tok, Token::Volatile) {
            consume!(self, Token::Volatile, "volatile");

            true
        } else {
            false
        };

        let ty = self.parse_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Ptr, "ptr");
        let ptr = self.parse_existing_value(b, ctx, Type::ptr())?;

        if !volatile {
            Ok(b.append().load(ty, ptr, dbg))
        } else {
            Ok(b.append().load_volatile(ty, ptr, dbg))
        }
    }

    fn parse_store_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, ()> {
        let dbg = self.debug();
        let next = self
            .lex
            .peek_token()
            .ok_or(Error::missing("expected volatile or type"))?;
        let volatile = if matches!(next.tok, Token::Volatile) {
            consume!(self, Token::Volatile, "volatile");

            true
        } else {
            false
        };

        let (_, storing) = self.parse_ty_val(b, ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Ptr, "ptr");
        let ptr = self.parse_existing_value(b, ctx, Type::ptr())?;

        let _ = if !volatile {
            b.append().store(storing, ptr, dbg)
        } else {
            b.append().store_volatile(storing, ptr, dbg)
        };

        Ok(())
    }

    fn parse_offset_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Ptr, "ptr");
        let ptr = self.parse_existing_value(b, ctx, Type::ptr())?;
        consume!(self, Token::Comma, ",");
        let offset_ty = self.parse_int_ty(ctx)?;
        let offset = self.parse_existing_value(b, ctx, offset_ty)?;

        Ok(b.append().offset(ty, ptr, offset, dbg))
    }

    fn parse_extract_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let output_ty = self.parse_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        let ty = self.parse_compound_ty(ctx)?;
        let val = self.parse_existing_value(b, ctx, ty)?;
        consume!(self, Token::Comma, ",");
        let index = self.parse_int_literal(64)?;

        Ok(b.append().extract(output_ty, val, index, dbg))
    }

    fn parse_insert_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_compound_ty(ctx)?;
        let val = self.parse_existing_value(b, ctx, ty)?;
        consume!(self, Token::Comma, ",");
        let (_, inserting) = self.parse_ty_val(b, ctx)?;
        consume!(self, Token::Comma, ",");
        let index = self.parse_int_literal(64)?;

        Ok(b.append().insert(val, inserting, index, dbg))
    }

    fn parse_elemptr_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_compound_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Ptr, "ptr");
        let ptr = self.parse_existing_value(b, ctx, Type::ptr())?;
        consume!(self, Token::Comma, ",");
        let index = self.parse_int_literal(64)?;

        Ok(b.append().elemptr(ty, ptr, index, dbg))
    }

    fn parse_int_to_int_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        opcode: Opcode,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let into = self.parse_int_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        let from_ty = self.parse_int_ty(ctx)?;
        let from = self.parse_existing_value(b, ctx, from_ty)?;

        match opcode {
            Opcode::Sext => Ok(b.append().sext(into, from, dbg)),
            Opcode::Zext => Ok(b.append().zext(into, from, dbg)),
            Opcode::Trunc => Ok(b.append().trunc(into, from, dbg)),
            _ => unreachable!(),
        }
    }

    fn parse_itob_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        consume!(self, Token::Bool, "bool");
        consume!(self, Token::Comma, ",");
        let ty = self.parse_int_ty(ctx)?;
        let from = self.parse_existing_value(b, ctx, ty)?;

        Ok(b.append().itob(from, dbg))
    }

    fn parse_btoi_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let into = self.parse_int_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Bool, "bool");
        let from = self.parse_existing_value(b, ctx, Type::bool())?;

        Ok(b.append().btoi(into, from, dbg))
    }

    fn parse_int_to_float_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        opcode: Opcode,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let into = self.parse_float_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        let from_ty = self.parse_int_ty(ctx)?;
        let from = self.parse_existing_value(b, ctx, from_ty)?;

        match opcode {
            Opcode::SIToF => Ok(b.append().sitof(into, from, dbg)),
            Opcode::UIToF => Ok(b.append().uitof(into, from, dbg)),
            _ => unreachable!(),
        }
    }

    fn parse_float_to_int_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        opcode: Opcode,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let into = self.parse_int_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        let from_ty = self.parse_float_ty(ctx)?;
        let from = self.parse_existing_value(b, ctx, from_ty)?;

        match opcode {
            Opcode::FToSI => Ok(b.append().ftosi(into, from, dbg)),
            Opcode::FToUI => Ok(b.append().ftoui(into, from, dbg)),
            _ => unreachable!(),
        }
    }

    fn parse_float_to_float_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
        opcode: Opcode,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let into = self.parse_float_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        let from_ty = self.parse_float_ty(ctx)?;
        let from = self.parse_existing_value(b, ctx, from_ty)?;

        match opcode {
            Opcode::FExt => Ok(b.append().fext(into, from, dbg)),
            Opcode::FTrunc => Ok(b.append().ftrunc(into, from, dbg)),
            _ => unreachable!(),
        }
    }

    fn parse_itop_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        consume!(self, Token::Ptr, "ptr");
        consume!(self, Token::Comma, ",");
        let ty = self.parse_int_ty(ctx)?;
        let from = self.parse_existing_value(b, ctx, ty)?;

        Ok(b.append().itop(from, dbg))
    }

    fn parse_ptoi_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let into = self.parse_int_ty(ctx)?;
        consume!(self, Token::Comma, ",");
        consume!(self, Token::Ptr, "ptr");
        let from = self.parse_existing_value(b, ctx, Type::ptr())?;

        Ok(b.append().ptoi(into, from, dbg))
    }

    fn parse_iconst_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_int_ty(ctx)?;
        let width = ty.as_int().unwrap().width();
        let value = self.parse_int_literal(width)?;

        Ok(b.append().iconst(ty, value, dbg))
    }

    fn parse_fconst_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_float_ty(ctx)?;
        let format = ty.as_float().unwrap().format();
        let float_lit = self.next("floating-point literal")?;

        let raw = match format {
            FloatFormat::Single => {
                let f32_val = match float_lit.tok {
                    Token::FloatLitNaN => Ok(f32::NAN),
                    Token::FloatLitStandard(lit) | Token::FloatLitScientific(lit) => {
                        f32::from_str(lit).map_err(|err| Error::err(float_lit, err.to_string()))
                    }
                    Token::FloatLitRaw(lit) => {
                        let raw = lit.trim_start_matches("0f");

                        // directly cast the bytes into a float, that's the point of this literal
                        u32::from_str_radix(raw, 16)
                            .map(f32::from_bits)
                            .map_err(|err| Error::err(float_lit, err.to_string()))
                    }
                    _ => Err(Error::unexpected(float_lit, "floating-point literal")),
                };

                (f32_val?).to_bits() as u64
            }
            FloatFormat::Double => {
                let f64_val = match float_lit.tok {
                    Token::FloatLitNaN => Ok(f64::NAN),
                    Token::FloatLitStandard(lit) | Token::FloatLitScientific(lit) => {
                        f64::from_str(lit).map_err(|err| Error::err(float_lit, err.to_string()))
                    }
                    Token::FloatLitRaw(lit) => {
                        let raw = lit.trim_start_matches("0f");

                        // directly cast the bytes into a float, that's the point of this literal
                        u64::from_str_radix(raw, 16)
                            .map(f64::from_bits)
                            .map_err(|err| Error::err(float_lit, err.to_string()))
                    }
                    _ => Err(Error::unexpected(float_lit, "floating-point literal")),
                };

                (f64_val?).to_bits()
            }
        };

        Ok(b.append().fconst_raw(ty, raw, dbg))
    }

    fn parse_bconst_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        consume!(self, Token::Bool, "bool");
        let next = consume!(self, Token::BoolLit(_), "true or false");
        let val = match next.tok {
            Token::BoolLit(true) => true,
            Token::BoolLit(false) => false,
            _ => unreachable!(),
        };

        Ok(b.append().bconst(val, dbg))
    }

    fn parse_undef_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_ty(ctx)?;

        Ok(b.append().undef(ty, dbg))
    }

    fn parse_null_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let ty = self.parse_ty(ctx)?;

        Ok(b.append().null(ty, dbg))
    }

    fn parse_stack_slot_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        let dbg = self.debug();
        let name = self.parse_stack_ident()?;
        let tok = self.current.unwrap();
        let slot = match self.stack_lookup.get(name) {
            Some(slot) => slot,
            None => return Err(Error::err(tok, format!("unknown stack slot '${name}'"))),
        };

        Ok(b.append().stackslot(*slot, dbg))
    }

    fn parse_global_addr_instruction(
        &mut self,
        b: &mut FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Value> {
        todo!()
    }

    #[inline]
    fn parse_ty_val_at_current(
        &mut self,
        b: &FuncBuilder<'_>,
        ctx: &ModuleContext,
        pair: TokPair<'a>,
    ) -> ParseResult<'a, (Type, Value)> {
        let ty = self.parse_ty_at_current(pair, ctx)?;
        let val = self.parse_existing_value(b, ctx, ty)?;

        Ok((ty, val))
    }

    #[inline]
    fn parse_ty_val(
        &mut self,
        b: &FuncBuilder<'_>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, (Type, Value)> {
        let ty = self.parse_ty(ctx)?;
        let val = self.parse_existing_value(b, ctx, ty)?;

        Ok((ty, val))
    }

    #[inline]
    fn parse_binop_lhs_rhs(
        &mut self,
        b: &FuncBuilder<'_>,
        ctx: &ModuleContext,
        ty: Type,
    ) -> ParseResult<'a, (Value, Value)> {
        let lhs = self.parse_existing_value(b, ctx, ty)?;
        consume!(self, Token::Comma, ",");
        let rhs = self.parse_existing_value(b, ctx, ty)?;

        Ok((lhs, rhs))
    }

    fn insert_new_value(
        &mut self,
        pair: TokPair<'a>,
        name: &'a str,
        val: Value,
    ) -> ParseResult<'a, ()> {
        if let Ok(value) = usize::from_str(name) {
            if value != self.next_inst {
                return Err(Error::err(
                    pair,
                    format!(
                        "expected next instruction to be numbered '%{}' but got '%{value}'",
                        self.next_inst
                    ),
                ));
            } else {
                self.next_inst += 1;
            }
        }

        self.local_lookup.insert(name, val);

        Ok(())
    }

    fn parse_existing_value(
        &mut self,
        b: &FuncBuilder<'_>,
        ctx: &ModuleContext,
        ty: Type,
    ) -> ParseResult<'a, Value> {
        let name = self.parse_local_ident()?;

        match self.local_lookup.get(name) {
            Some(value) => {
                let real = b.ty(*value);

                if real != ty {
                    Err(Error::wrong_type(self.current.unwrap(), ty, real, ctx))
                } else {
                    Ok(*value)
                }
            }
            None => Err(Error::message(
                self.current.unwrap(),
                "unknown value, values must be defined before use",
            )),
        }
    }

    // parses a global identifier
    fn parse_global_ident(&mut self) -> ParseResult<'a, &'a str> {
        let next = self.next("global identifier")?;

        if let Token::GlobalIdent(name) = next.tok {
            Ok(name)
        } else {
            Err(Error::unexpected(next, "global identifier"))
        }
    }

    // parses a local identifier, and updates self.value_name
    fn parse_new_local_ident(&mut self, ctx: &ModuleContext) -> ParseResult<'a, &'a str> {
        let ident = self.parse_local_ident()?;

        if ident.chars().any(|c| !c.is_ascii_digit()) {
            self.value_name = Some(ctx.strings_mut().insert(ident));
        } else {
            self.value_name = None;
        }

        Ok(ident)
    }

    // parses a local identifier
    fn parse_local_ident(&mut self) -> ParseResult<'a, &'a str> {
        let next = self.next("local identifier")?;

        match next.tok {
            Token::LocalIdent(name) => Ok(name),
            _ => Err(Error::unexpected(next, "local identifier")),
        }
    }

    // parses a stack identifier
    fn parse_stack_ident(&mut self) -> ParseResult<'a, &'a str> {
        let next = self.next("stack identifier")?;

        if let Token::StackIdent(name) = next.tok {
            Ok(name)
        } else {
            Err(Error::unexpected(next, "stack identifier"))
        }
    }

    // parses a stack identifier
    fn parse_label_ident(&mut self) -> ParseResult<'a, &'a str> {
        let next = self.next("label identifier")?;

        Self::parse_peeked_label_ident(next)
    }

    fn parse_peeked_label_ident(pair: TokPair<'a>) -> ParseResult<'a, &'a str> {
        match pair.tok {
            Token::LabelIdent(name) => Ok(name),
            Token::CmpOpcode(opc) => Ok(match opc {
                CompareOpcode::Eq => "eq",
                CompareOpcode::Ne => "ne",
                CompareOpcode::Ugt => "ugt",
                CompareOpcode::Ult => "ult",
                CompareOpcode::Uge => "uge",
                CompareOpcode::Ule => "ule",
                CompareOpcode::Sgt => "sgt",
                CompareOpcode::Slt => "slt",
                CompareOpcode::Sge => "sge",
                CompareOpcode::Sle => "sle",
                CompareOpcode::Ord => "ord",
                CompareOpcode::Uno => "uno",
                CompareOpcode::Ueq => "ueq",
                CompareOpcode::Une => "une",
                CompareOpcode::Oeq => "oeq",
                CompareOpcode::One => "one",
                CompareOpcode::Ogt => "ogt",
                CompareOpcode::Olt => "olt",
                CompareOpcode::Oge => "oge",
                CompareOpcode::Ole => "ole",
            }),
            _ => Err(Error::unexpected(pair, "label identifier")),
        }
    }

    // parses a type starting at the next token
    fn parse_ty(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let pair = self.next("type")?;

        self.parse_ty_at_current(pair, ctx)
    }

    // parses an integral or bool type
    #[inline]
    fn parse_ptr_bool_or_int_ty(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let ty = self.parse_ty(ctx)?;

        if ty.is_bool_or_int() || ty.is_ptr() {
            Ok(ty)
        } else {
            Err(Error::unexpected(
                self.current.unwrap(),
                "ptr, bool or int type",
            ))
        }
    }

    // parses an integral or bool type
    #[inline]
    fn parse_int_or_bool_ty(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let ty = self.parse_ty(ctx)?;

        if ty.is_bool_or_int() {
            Ok(ty)
        } else {
            Err(Error::unexpected(self.current.unwrap(), "bool or int type"))
        }
    }

    // parses an integral type
    #[inline]
    fn parse_int_ty(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let ty = self.parse_ty(ctx)?;

        if ty.is_int() {
            Ok(ty)
        } else {
            Err(Error::unexpected(self.current.unwrap(), "int type"))
        }
    }

    // parses a floating-point type
    #[inline]
    fn parse_float_ty(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let ty = self.parse_ty(ctx)?;

        if ty.is_float() {
            Ok(ty)
        } else {
            Err(Error::unexpected(self.current.unwrap(), "float type"))
        }
    }

    // parses a compound (array or structure) type
    #[inline]
    fn parse_compound_ty(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let ty = self.parse_ty(ctx)?;

        if ty.is_array() || ty.is_struct() {
            Ok(ty)
        } else {
            Err(Error::unexpected(
                self.current.unwrap(),
                "array or structure type",
            ))
        }
    }

    // parses a type starting at the last yielded token (given via `pair`)
    fn parse_ty_at_current(
        &mut self,
        pair: TokPair<'a>,
        ctx: &ModuleContext,
    ) -> ParseResult<'a, Type> {
        match pair.tok {
            Token::Bool => Ok(Type::bool()),
            Token::Ptr => Ok(Type::ptr()),
            Token::I8 => Ok(Type::i8()),
            Token::I16 => Ok(Type::i16()),
            Token::I32 => Ok(Type::i32()),
            Token::I64 => Ok(Type::i64()),
            Token::F32 => Ok(Type::f32()),
            Token::F64 => Ok(Type::f64()),
            Token::SquareOpen => self.parse_array_ty_at_current(ctx),
            Token::CurlyOpen => self.parse_struct_ty_at_current(ctx),
            _ => Err(Error::unexpected(pair, "type")),
        }
    }

    // internal array type parser, assumes the '[' has already been consumed
    fn parse_array_ty_at_current(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let inner = self.parse_ty(ctx)?;
        consume!(self, Token::X, "x");
        let elements = self.parse_int_literal(64)?;
        consume!(self, Token::SquareClose, "]");

        Ok(Type::array(&mut ctx.types_mut(), inner, elements))
    }

    // internal struct type parser, assumes the '{' has already been consumed
    fn parse_struct_ty_at_current(&mut self, ctx: &ModuleContext) -> ParseResult<'a, Type> {
        let mut comma_count = 0;
        let mut types = SmallVec::<[Type; 8]>::default();

        loop {
            let next = self.next("type or '}'")?;

            match next.tok {
                Token::CurlyClose => got_closing_symbol!(comma_count, next, "type"),
                Token::Comma => got_comma!(comma_count, next, "type or '}'"),
                _ => {
                    needed_comma_previously!(comma_count, next);

                    types.push(self.parse_ty_at_current(next, ctx)?);
                }
            }
        }

        Ok(Type::structure(&mut ctx.types_mut(), &types))
    }

    fn parse_int_literal(&mut self, width: u32) -> ParseResult<'a, u64> {
        let next = self.next("integer literal")?;
        let maybe_u64 = match next.tok {
            Token::IntLitDecimal(base10) => {
                if base10.starts_with('-') {
                    //
                    // this is horrific but it is necessary to get the behavior we want here
                    //
                    // in cases like `iconst i8 -1`, we want `0xFF` to be the value we get,
                    // so this necessitates the cast process i8 -> u8 -> u64 instead of i8 -> u64
                    //
                    // the latter case gets turned into a sign extension by Rust, which would
                    // make the value be `0xFFFFFFFFFFFFFFFF` instead of `0xFF`
                    //
                    let val = match width {
                        8 => {
                            let val = match base10.parse::<i8>() {
                                Ok(val) => val,
                                Err(err) => return Err(Error::err(next, err.to_string())),
                            };

                            val as u8 as u64
                        }
                        16 => {
                            let val = match base10.parse::<i16>() {
                                Ok(val) => val,
                                Err(err) => return Err(Error::err(next, err.to_string())),
                            };

                            val as u16 as u64
                        }
                        32 => {
                            let val = match base10.parse::<i32>() {
                                Ok(val) => val,
                                Err(err) => return Err(Error::err(next, err.to_string())),
                            };

                            val as u32 as u64
                        }
                        64 => {
                            let val = match base10.parse::<i64>() {
                                Ok(val) => val,
                                Err(err) => return Err(Error::err(next, err.to_string())),
                            };

                            val as u64
                        }
                        _ => unreachable!(),
                    };

                    Ok(val)
                } else {
                    base10.parse::<u64>()
                }
            }
            Token::IntLitBinary(base2) => u64::from_str_radix(base2, 2),
            Token::IntLitHex(base16) => u64::from_str_radix(base16, 16),
            Token::IntLitOctal(base8) => u64::from_str_radix(base8, 8),
            _ => return Err(Error::unexpected(next, "integer literal")),
        };

        maybe_u64.map_err(|err| Error::err(next, err.to_string()))
    }

    #[inline]
    fn debug(&self) -> DebugInfo {
        let curr = self.current.unwrap();

        match self.value_name {
            Some(name) => DebugInfo::with_name(name, curr.line, curr.col as u32, self.name_ref),
            None => DebugInfo::new(curr.line, curr.col as u32, self.name_ref),
        }
    }

    fn next(&mut self, message: &'static str) -> ParseResult<'a, TokPair<'a>> {
        match self.lex.next_token() {
            Some(pair) => {
                self.current = Some(pair);

                Ok(pair)
            }
            None => Err(match self.current {
                Some(pair) => Error::err(pair, format!("expected token '{message}' but got EOF")),
                None => Error::missing("file is completely empty"),
            }),
        }
    }
}

/// A parse error of some sort, this can be formatted by the caller
#[derive(Clone, Debug)]
pub struct Error<'a> {
    /// The token, if one exists
    pub pair: Option<TokPair<'a>>,
    /// The error message
    pub error: String,
}

impl<'a> Error<'a> {
    fn message(pair: TokPair<'a>, message: &'static str) -> Self {
        Self {
            pair: Some(pair),
            error: message.to_string(),
        }
    }

    fn err(pair: TokPair<'a>, error: String) -> Self {
        Self {
            pair: Some(pair),
            error,
        }
    }

    fn missing(error: &'static str) -> Self {
        Self {
            pair: None,
            error: error.to_string(),
        }
    }

    fn unexpected(pair: TokPair<'a>, expected: &'static str) -> Self {
        Self {
            pair: Some(pair),
            error: format!(
                "expected token '{expected}' but got this instead: '{:?}'",
                pair.tok
            ),
        }
    }

    fn wrong_type(pair: TokPair<'a>, expected: Type, got: Type, ctx: &ModuleContext) -> Self {
        let (expected, got) = {
            let ty_pool = ctx.types();

            (
                analysis::stringify_ty(&ty_pool, expected),
                analysis::stringify_ty(&ty_pool, got),
            )
        };

        Self {
            pair: Some(pair),
            error: format!("expected type of value to be '{expected}' but actually is '{got}'"),
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.pair {
            Some(pair) => {
                let (line, col) = (pair.line, pair.col);
                let err = &self.error;

                write!(f, "line {line}:{col}: {err}",)
            }
            None => {
                let err = &self.error;

                write!(f, "<empty file>: {err}",)
            }
        }
    }
}

impl<'a> std::error::Error for Error<'a> {}
