//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Contains the SIR grammar, SIR parser and a type-checker for the parsed SIR.
//!
//! This is effectively just a wrapper module around the `pest` grammar being
//! used to parse SIR text files, with type-checking strapped on to ensure
//! only valid IR is being parsed.

use crate::analysis::{stringify_signature, stringify_ty};
use crate::ir::*;
use crate::utility::{Packable, SaHashMap, Str};
use pest::error::ErrorVariant;
use pest::iterators::{Pair, Pairs};
use pest::{error::Error as PestErr, Parser, Span, Token};
use smallvec::SmallVec;
use std::error::Error;
use std::str::FromStr;

mod generated {
    // pest doesn't generate good documentation here
    #![allow(missing_docs)]

    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "sir.pest"]
    pub(crate) struct SIRReader;
}

type Rule = generated::Rule;

fn string_into_err(span: Span<'_>, message: String) -> Box<dyn Error> {
    let error = PestErr::new_from_span(ErrorVariant::<Rule>::CustomError { message }, span);

    Box::new(error).into()
}

fn message_into_err(span: Span<'_>, message: &str) -> Box<dyn Error> {
    string_into_err(span, String::from(message))
}

fn tok_into_info(tok: Token<'_, Rule>, file: Str, name: Option<Str>) -> DebugInfo {
    let pos = match tok {
        Token::Start { pos, .. } => pos,
        Token::End { pos, .. } => pos,
    };

    let (line, col) = pos.line_col();

    match name {
        Some(s) => DebugInfo::with_name(s, line as u32, col as u32, file),
        None => DebugInfo::new(line as u32, col as u32, file),
    }
}

fn pair_into_info(pair: Pair<'_, Rule>, file: Str, name: Option<Str>) -> DebugInfo {
    tok_into_info(pair.tokens().next().unwrap(), file, name)
}

trait IntoNextPair<'p>: Iterator<Item = Pair<'p, Rule>> {
    type InnerPairs;

    fn next_pairs_or(&mut self, message: &'static str) -> Self::InnerPairs;

    fn next_or(&mut self, message: &'static str) -> Self::Item;
}

impl<'p> IntoNextPair<'p> for Pairs<'p, Rule> {
    type InnerPairs = Pairs<'p, Rule>;

    fn next_pairs_or(&mut self, message: &'static str) -> Self::InnerPairs {
        self.next().expect(message).into_inner()
    }

    fn next_or(&mut self, message: &'static str) -> Self::Item {
        self.next().expect(message)
    }
}

type ParseResult<T> = Result<T, Box<dyn Error>>;

struct ResolveAppendBuilder<'f, 'p> {
    ident: LocalIdent,
    builder: AppendBuilder<'f>,
    parser: &'p mut SIRParser,
}

impl<'f, 'p> InstBuilder<'f> for ResolveAppendBuilder<'f, 'p> {
    fn dfg(&self) -> &DataFlowGraph {
        self.builder.dfg()
    }

    fn build(self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>) {
        let (inst, val) = self.builder.build(data, debug);

        match val {
            Some(val) => self.parser.resolver.insert(self.ident, val),
            None => unreachable!(),
        };

        (inst, val)
    }
}

#[derive(Hash, PartialEq, Eq)]
enum LocalIdent {
    Num(u32),
    Name(Str),
}

struct SIRParser {
    next: u32,
    filename: Str,
    resolver: SaHashMap<LocalIdent, Value>,
}

impl SIRParser {
    fn parse(filename: &str, pairs: Pairs<'_, Rule>) -> ParseResult<Module> {
        let mut module = Module::new(filename);

        let mut obj = Self {
            filename: Str::reserved(),
            next: 0,
            resolver: SaHashMap::default(),
        };

        obj.filename = module.insert_string(filename);

        obj.sir(&mut module, pairs)?;

        Ok(module)
    }

    fn sir(&mut self, module: &mut Module, mut pairs: Pairs<'_, Rule>) -> ParseResult<()> {
        // parsing function bodies is delayed to allow all functions to be declared, necessary
        // for later calls/global-addrs, so we push them into a vec here while we parse/declare
        // all the prototypes, and then we go parse all of those afterwards.
        let mut delayed = Vec::default();
        let sir = pairs.next_or("expected sir");
        let inner = sir.into_inner();

        for pair in inner {
            match pair.as_rule() {
                Rule::function => {
                    let value = self.preprocess_func(module, pair)?;

                    delayed.push(value);
                }
                Rule::EOI => {}
                _ => unreachable!(),
            }
        }

        for (func, body) in delayed
            .into_iter()
            .filter(|(_, body)| body.is_some())
            .map(|(func, body)| (func, body.unwrap()))
        {
            let builder = module.define_existing_function(func);

            self.parse_func_body(body, builder)?;
        }

        Ok(())
    }

    // parses the prototype of a function, and returns the body if there is one.
    // parsing the body is delayed to allow all functions to be declared, necessary
    // for later calls/global-addrs
    fn preprocess_func<'a>(
        &mut self,
        module: &mut Module,
        pair: Pair<'a, Rule>,
    ) -> ParseResult<(Func, Option<Pair<'a, Rule>>)> {
        debug_assert!(matches!(pair.as_rule(), Rule::function));

        let mut pairs = pair.into_inner();
        let proto = pairs.next_or("expected a function prototype");
        let (name, sig) = self.parse_func_proto(proto, module.type_pool_mut())?;
        let key = module.declare_function(&name, sig);

        Ok((key, pairs.next()))
    }

    // parses the function prototype (the `fn T @name(...) abi` part) and returns the name/signature
    fn parse_func_proto(
        &mut self,
        pair: Pair<'_, Rule>,
        pool: &mut TypePool,
    ) -> ParseResult<(String, Signature)> {
        debug_assert!(matches!(pair.as_rule(), Rule::function_prototype));

        let mut proto = pair.into_inner();

        let ty_or_void = proto.next_or("expected a type or `void`");

        let global_ident = proto.next_or("expected a global name");
        let name = self.parse_global(global_ident)?;

        let return_ty = self.parse_ty_or_void(ty_or_void, pool)?;
        let param_list = proto.next_or("expected a parameter list");
        let (params, variadic) = self.parse_param_list(param_list, pool)?;
        let abi = self.parse_abi(proto.next())?;

        let sig = SigBuilder::new()
            .ret(return_ty)
            .params(&params)
            .vararg(variadic)
            .abi(abi)
            .build();

        Ok((name, sig))
    }

    // parses a function's abi if it has one
    fn parse_abi(&mut self, pair: Option<Pair<'_, Rule>>) -> ParseResult<CallConv> {
        let pair = match pair {
            Some(pair) => pair,
            None => return Ok(CallConv::C),
        };

        debug_assert!(matches!(pair.as_rule(), Rule::abi));

        match pair.as_str() {
            "ccc" => Ok(CallConv::C),
            "sysv" => Ok(CallConv::SysV),
            "win64" => Ok(CallConv::Win64),
            "fastcc" => Ok(CallConv::Fast),
            _ => unreachable!(),
        }
    }

    // parses a function prototype's parameter list. returns the parameter types and whether
    // or not the function is variadic
    fn parse_param_list(
        &mut self,
        pair: Pair<'_, Rule>,
        pool: &mut TypePool,
    ) -> ParseResult<(Vec<Type>, bool)> {
        debug_assert!(matches!(pair.as_rule(), Rule::param_list));

        let mut inner = pair.into_inner();
        let next = match inner.next() {
            Some(pair) => pair,
            None => return Ok((vec![], false)),
        };

        let list = match next.as_rule() {
            Rule::ty_list => self.parse_ty_list(next, pool)?,
            Rule::variadic => return Ok((vec![], true)),
            _ => unreachable!(),
        };

        match inner.next() {
            Some(pair) => {
                debug_assert!(matches!(pair.as_rule(), Rule::variadic));

                Ok((list, true))
            }
            None => Ok((list, false)),
        }
    }

    fn parse_func_body(
        &mut self,
        pair: Pair<'_, Rule>,
        mut builder: FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::function_body));

        self.next = 0;
        self.resolver.clear();

        // similar deal to how functions are pre-processed by the parser,
        // we need to go ahead and parse the blocks and form block nodes
        // inside of the function before we parse code that may potentially
        // jump between them.
        let mut delayed = Vec::default();
        let rest = pair.into_inner();

        for block in rest {
            delayed.push(self.preprocess_block(block, &mut builder)?);
        }

        for (block, label, body) in delayed
            .into_iter()
            .filter(|(_, _, body)| body.is_some())
            .map(|(block, label, body)| (block, label, body.unwrap()))
        {
            builder.switch_to(block);
            self.verify_block_label(label, &mut builder)?;
            self.parse_block_body(body, &mut builder)?;
        }

        builder.define();

        Ok(())
    }

    fn preprocess_block<'a>(
        &mut self,
        block: Pair<'a, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(Block, Pair<'a, Rule>, Option<Pairs<'a, Rule>>)> {
        let mut pairs = block.into_inner();
        let label = pairs.next_or("expected block label");
        let label_copy = label.clone();
        let span = label.as_span();
        let block = self.preprocess_block_label(label, builder)?;

        if builder.is_entry_block(block) {
            let sig = builder.current_signature();
            let block_params = builder.block_params(block);

            let param_tys = sig.params().iter().map(|(ty, _)| *ty);
            let block_param_tys = block_params.iter().map(|val| builder.ty(*val));

            if !param_tys.eq(block_param_tys) {
                return Err(message_into_err(
                    span,
                    "function parameters do not match parameters of entry block",
                ));
            }
        }

        Ok((block, label_copy, pairs.peek().map(|_| pairs)))
    }

    fn parse_block_body(
        &mut self,
        body: Pairs<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        for inst in body {
            self.parse_inst(inst, builder)?;
        }

        Ok(())
    }

    fn preprocess_block_label(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Block> {
        debug_assert!(matches!(pair.as_rule(), Rule::block_label));

        let mut pairs = pair.into_inner();
        let ident = pairs.next_or("expected ident");

        debug_assert!(matches!(ident.as_rule(), Rule::ident));

        let block = builder.create_block(ident.as_str());

        if let Some(params) = pairs.next() {
            // we take a pair for the name here instead of a LocalIdent, because we need
            // the debuginfo just as much as we need the actual name.
            for (ty, ident) in self.parse_operand_list(params, builder.type_pool_mut())? {
                let (ident, debug) = self.preprocess_block_param_local(ident, builder)?;
                let param = builder.append_block_param(block, ty, debug);

                self.resolver.insert(ident, param);
            }
        }

        Ok(block)
    }

    //
    fn verify_block_label(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::block_label));

        let mut pairs = pair.into_inner();
        let ident = pairs.next_or("expected ident");

        debug_assert!(matches!(ident.as_rule(), Rule::ident));

        if let Some(params) = pairs.next() {
            // we take a pair for the name here instead of a LocalIdent, because we need
            // the debuginfo just as much as we need the actual name.
            for (_, ident) in self.parse_operand_list(params, builder.type_pool_mut())? {
                self.verify_block_param_local(ident, builder)?;
            }
        }

        Ok(())
    }

    fn parse_operand_list<'a>(
        &mut self,
        pair: Pair<'a, Rule>,
        pool: &mut TypePool,
    ) -> ParseResult<Vec<(Type, Pair<'a, Rule>)>> {
        let mut vec = Vec::default();
        let pairs = pair.into_inner();

        for operand in pairs {
            debug_assert!(matches!(operand.as_rule(), Rule::operand));

            let mut inner = operand.into_inner();
            let ty_pair = inner.next_or("expected type");
            let ty = self.parse_ty(ty_pair, pool)?;
            let ident = inner.next_or("expected ident for pair");

            vec.push((ty, ident));
        }

        Ok(vec)
    }

    fn parse_inst(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::inst));

        let inner = pair.into_inner().next_or("expected instruction");

        match inner.as_rule() {
            Rule::call => self.parse_call(inner, builder),
            Rule::indirectcall => self.parse_indirect_call(inner, builder),
            Rule::icmp => self.parse_icmp(inner, builder),
            Rule::fcmp => self.parse_fcmp(inner, builder),
            Rule::sel => self.parse_sel(inner, builder),
            Rule::br => self.parse_br(inner, builder),
            Rule::condbr => self.parse_condbr(inner, builder),
            Rule::unreachable => self.parse_unreachable(inner, builder),
            Rule::ret => self.parse_ret(inner, builder),
            Rule::binary_bitwise => self.parse_binary_bitwise(inner, builder),
            Rule::binary_int => self.parse_binary_int(inner, builder),
            Rule::fneg => self.parse_fneg(inner, builder),
            Rule::binary_float => self.parse_binary_float(inner, builder),
            Rule::alloca => self.parse_alloca(inner, builder),
            Rule::load => self.parse_load(inner, builder),
            Rule::store => self.parse_store(inner, builder),
            Rule::offset => self.parse_offset(inner, builder),
            Rule::extract => self.parse_extract(inner, builder),
            Rule::insert => self.parse_insert(inner, builder),
            Rule::elemptr => self.parse_elemptr(inner, builder),
            Rule::int_conv => self.parse_int_conv(inner, builder),
            Rule::itob => self.parse_itob(inner, builder),
            Rule::btoi => self.parse_btoi(inner, builder),
            Rule::int_to_float => self.parse_int_to_float(inner, builder),
            Rule::float_to_int => self.parse_float_to_int(inner, builder),
            Rule::float_conv => self.parse_float_conv(inner, builder),
            Rule::itop => self.parse_itop(inner, builder),
            Rule::ptoi => self.parse_ptoi(inner, builder),
            Rule::iconst => self.parse_iconst(inner, builder),
            Rule::fconst => self.parse_fconst(inner, builder),
            Rule::bconst => self.parse_bconst(inner, builder),
            Rule::undef => self.parse_undef(inner, builder),
            Rule::null => self.parse_null(inner, builder),
            Rule::globaladdr => self.parse_globaladdr(inner, builder),
            _ => unreachable!(),
        }
    }

    fn parse_call(
        &mut self,
        inner: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(inner.as_rule(), Rule::call));

        let pair = inner.clone();
        let mut pairs = inner.into_inner();
        let result = self.parse_optional_result(&mut pairs, builder)?;
        let ty = self.parse_ty_or_void(
            pairs.next_or("expected ty or void"),
            builder.type_pool_mut(),
        )?;

        let func = self.parse_func_name(pairs.next_or("expected func name"), builder)?;
        let signature = builder.function(func).signature().clone();

        match (signature.return_ty(), ty) {
            (Some(t1), Some(t2)) if t1 != t2 => {
                let msg = format!(
                    "mismatched return type, expected '{}' but got '{}'. signature of '{}' is '{}'",
                    stringify_ty(builder.type_pool(), t1),
                    stringify_ty(builder.type_pool(), t2),
                    builder.function(func).name(),
                    stringify_signature(builder.type_pool(), &signature)
                );

                return Err(string_into_err(pair.as_span(), msg));
            }
            _ => {}
        }

        let args = self.parse_arg_with_types(
            &signature,
            pairs.next_or("expected call arguments"),
            builder,
        )?;

        let sig = builder.import_signature(&signature);
        let name = match &result {
            Some((LocalIdent::Name(s), _)) => Some(*s),
            _ => None,
        };

        let info = pair_into_info(pair.clone(), self.filename, name);
        let inst = builder.append().call(func, sig, &args, info);

        self.check_result_of_call(pair.as_span(), inst, result, builder)
    }

    fn check_result_of_call(
        &mut self,
        span: Span<'_>,
        inst: Inst,
        result: Option<(LocalIdent, DebugInfo)>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        // check to make sure that the user gave the result a name
        // if the function is non-void
        match (builder.inst_to_result(inst), result) {
            // void function, no result in code
            (None, None) => Ok(()),
            // non-void, has result in code
            (Some(val), Some((ident, _))) => {
                self.resolver.insert(ident, val);

                Ok(())
            }
            // non-void, no result in code
            (Some(_), None) => Err(message_into_err(
                span,
                "call to non-'void' function must have a result",
            )),
            // void, has result in code
            (None, Some(_)) => Err(message_into_err(
                span,
                "call to 'void' function cannot have a result",
            )),
        }
    }

    fn parse_func_name(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Func> {
        let span = pair.as_span();
        let name = self.parse_global(pair)?;

        match builder.find_function_by_name(&name) {
            Some(func) => Ok(func),
            None => Err(string_into_err(span, format!("unknown function '{name}'"))),
        }
    }

    // lol
    #[allow(clippy::too_many_arguments)]
    #[inline]
    fn parse_generic_arg_with_types<'a, I, F1, F2, F3>(
        &mut self,
        pair: Pair<'a, Rule>,
        builder: &mut FuncBuilder<'_>,
        mut param_tys: I,
        vararg: bool,
        mismatch: F1,
        unexpected: F2,
        missing: F3,
    ) -> ParseResult<Vec<Value>>
    where
        I: Iterator<Item = Type> + ExactSizeIterator,
        F1: FnOnce(&'a str, Type, Type, &FuncBuilder<'_>) -> ParseResult<Vec<Value>>,
        F2: FnOnce(&'a str, &FuncBuilder<'_>) -> ParseResult<Vec<Value>>,
        F3: FnOnce(usize, usize, &FuncBuilder<'_>) -> ParseResult<Vec<Value>>,
    {
        debug_assert!(matches!(pair.as_rule(), Rule::args_with_types));

        let expected = param_tys.len();
        let clone = pair.clone();
        let inner = pair.into_inner();
        let mut vec = Vec::default();
        let mut count = 0;

        for operand in inner {
            let val = self.parse_operand(operand, builder)?;

            match (param_tys.next(), builder.ty(val)) {
                // type mismatch, type in position didn't match expected type
                (Some(t1), t2) if t1 != t2 => {
                    return mismatch(clone.as_str(), t1, t2, builder);
                }
                // unexpected argument, sig said we should be done but we got more
                (None, _) if !vararg => {
                    return unexpected(clone.as_str(), builder);
                }
                // no issues
                _ => {
                    count += 1;
                }
            }

            vec.push(val);
        }

        if count != expected && !vararg {
            return missing(count, expected, builder);
        }

        Ok(vec)
    }

    fn parse_block_arg_with_types(
        &mut self,
        block: Block,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Vec<Value>> {
        debug_assert!(matches!(pair.as_rule(), Rule::args_with_types));

        let params: SmallVec<[Type; 16]> = builder
            .block_params(block)
            .iter()
            .map(|val| builder.ty(*val))
            .collect();

        let span = pair.as_span();

        let mismatch = |val, t1, t2, builder: &FuncBuilder<'_>| {
            let name = builder.block_name(block);
            let ty1 = stringify_ty(builder.type_pool(), t1);
            let ty2 = stringify_ty(builder.type_pool(), t2);
            let err = string_into_err(span, format!(
                "while parsing args for block '{name}', mismatched types for value '{val}', expected '{ty1}' but got '{ty2}'",
            ));

            Err(err)
        };

        let unexpected = |val, builder: &FuncBuilder<'_>| {
            let name = builder.block_name(block);
            let err = string_into_err(
                span,
                format!("while parsing args for block '{name}', unexpected parameter '{val}'",),
            );

            Err(err)
        };

        let missing = |count, expected, builder: &FuncBuilder<'_>| {
            let name = builder.block_name(block);
            let err = string_into_err(span, format!(
                "not enough arguments given for block '{name}', got {count} args but expected {expected}"
            ));

            Err(err)
        };

        self.parse_generic_arg_with_types(
            pair,
            builder,
            params.into_iter(),
            false,
            mismatch,
            unexpected,
            missing,
        )
    }

    fn parse_arg_with_types(
        &mut self,
        sig: &Signature,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Vec<Value>> {
        debug_assert!(matches!(pair.as_rule(), Rule::args_with_types));

        let params = sig.params().iter().map(|(ty, _)| *ty);
        let span = pair.as_span();

        let mismatch = |name, t1, t2, builder: &FuncBuilder<'_>| {
            let msg = format!(
                        "while parsing args for function with signature '{}', mismatched types for value '{}', expected '{}' but got '{}'",
                        stringify_signature(builder.type_pool(), sig),
                        name,
                        stringify_ty(builder.type_pool(), t1),
                        stringify_ty(builder.type_pool(), t2)
                    );

            let err = string_into_err(span, msg);

            Err(err)
        };

        let unexpected = |name, builder: &FuncBuilder<'_>| {
            let msg = format!(
                "while parsing args for function with signature '{}', unexpected parameter '{}'",
                stringify_signature(builder.type_pool(), sig),
                name,
            );

            let err = string_into_err(span, msg);

            Err(err)
        };

        let missing = |count, expected, builder: &FuncBuilder<'_>| {
            let sig = stringify_signature(builder.type_pool(), sig);
            let msg = format!(
                "while parsing args for function with signature '{sig}', \
expected {expected} arguments but got {count}"
            );

            let err = string_into_err(span, msg);

            Err(err)
        };

        self.parse_generic_arg_with_types(
            pair,
            builder,
            params,
            sig.vararg(),
            mismatch,
            unexpected,
            missing,
        )
    }

    fn parse_indirect_call(
        &mut self,
        inner: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(inner.as_rule(), Rule::indirectcall));

        let pair = inner.clone();
        let mut inner = inner.into_inner();
        let result = self.parse_optional_result(&mut inner, builder)?;
        let sig = self.parse_signature(inner.next_or("expected signature"), builder)?;

        let _ = inner.next_or("expected ptr_ty");

        let callee = self.parse_existing_local_of_ty(
            inner.next_or("expected operand"),
            Type::ptr(),
            builder,
        )?;

        let signature = builder.signature(sig).clone();
        let args = self.parse_arg_with_types(
            &signature, //
            inner.next_or("expected args"),
            builder,
        )?;

        let name = match &result {
            Some((LocalIdent::Name(s), _)) => Some(*s),
            _ => None,
        };

        let info = pair_into_info(pair.clone(), self.filename, name);
        let inst = builder.append().indirectcall(callee, sig, &args, info);

        self.check_result_of_call(pair.as_span(), inst, result, builder)
    }

    fn parse_signature(
        &mut self,
        inner: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Sig> {
        debug_assert!(matches!(inner.as_rule(), Rule::signature));

        let mut inner = inner.into_inner();
        let ret = self.parse_ty_or_void(
            inner.next_or("expected ty or void"),
            builder.type_pool_mut(),
        )?;

        let (params, variadic) = self.parse_param_list(
            inner.next_or("expected param list"),
            builder.type_pool_mut(),
        )?;

        let params: SmallVec<[(Type, ParamAttributes); 2]> = params
            .into_iter()
            .map(|param| (param, ParamAttributes::empty()))
            .collect();

        let sig = Signature::new(params, (ret, RetAttributes::empty()), CallConv::C, variadic);

        Ok(builder.import_signature(&sig))
    }

    fn parse_icmp(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::icmp));

        let mut inner = pair.into_inner();
        let (ident, info) = self.parse_result(inner.next_or("expected result"), builder)?;
        let opc = match inner.next_or("expected opcode").as_str() {
            "eq" => ICmpOp::EQ,
            "ne" => ICmpOp::NE,
            "ugt" => ICmpOp::UGT,
            "ult" => ICmpOp::ULT,
            "uge" => ICmpOp::UGE,
            "ule" => ICmpOp::ULE,
            "sgt" => ICmpOp::SGT,
            "slt" => ICmpOp::SLT,
            "sge" => ICmpOp::SGE,
            "sle" => ICmpOp::SLE,
            _ => unreachable!(),
        };

        let (lhs, rhs) = self.parse_existing_bitwise_binary_ops(&mut inner, builder)?;

        self.append_val(builder, ident).icmp(opc, lhs, rhs, info);

        Ok(())
    }

    fn parse_fcmp(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::fcmp));

        let mut inner = pair.into_inner();
        let (ident, info) = self.parse_result(inner.next_or("expected result"), builder)?;
        let opc = match inner.next_or("expected opcode").as_str() {
            "ord" => FCmpOp::ORD,
            "uno" => FCmpOp::UNO,
            "oeq" => FCmpOp::OEQ,
            "one" => FCmpOp::ONE,
            "ogt" => FCmpOp::OGT,
            "olt" => FCmpOp::OLT,
            "oge" => FCmpOp::OGE,
            "ole" => FCmpOp::OLE,
            "ueq" => FCmpOp::UEQ,
            "une" => FCmpOp::UNE,
            "ugt" => FCmpOp::UGT,
            "ult" => FCmpOp::ULT,
            "uge" => FCmpOp::UGE,
            "ule" => FCmpOp::ULE,
            _ => unreachable!(),
        };

        let (lhs, rhs) = self.parse_existing_float_binary_ops(&mut inner, builder)?;

        self.append_val(builder, ident).fcmp(opc, lhs, rhs, info);

        Ok(())
    }

    fn parse_sel(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::sel));

        let mut inner = pair.into_inner();
        let (ident, info) = self.parse_result(inner.next_or("expected result"), builder)?;
        let ty = self.parse_ty(inner.next_or("expected type"), builder.type_pool_mut())?;
        let _ = inner.next_or("expected bool_ty");
        let condition_pair = inner.next_or("expected local");
        let if_true_pair = inner.next_or("expected local");
        let if_false_pair = inner.next_or("expected local");

        let cond = self.parse_existing_local_of_ty(condition_pair, Type::bool(), builder)?;
        let if_true = self.parse_existing_local_of_ty(if_true_pair, ty, builder)?;
        let if_false = self.parse_existing_local_of_ty(if_false_pair, ty, builder)?;

        self.append_val(builder, ident)
            .sel(cond, if_true, if_false, info);

        Ok(())
    }

    fn parse_br(&mut self, pair: Pair<'_, Rule>, builder: &mut FuncBuilder<'_>) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::br));

        let info = pair_into_info(pair.clone(), self.filename, None);
        let mut inner = pair.into_inner();
        let target_pair = inner.next_or("expected a branch target");

        let target = self.parse_block_target(target_pair, builder)?;

        builder.append().br(target, info);

        Ok(())
    }

    fn parse_condbr(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::condbr));

        let info = pair_into_info(pair.clone(), self.filename, None);
        let mut inner = pair.into_inner();
        let _ = inner.next_or("expected bool_ty");
        let local_pair = inner.next_or("expected operand");
        let if_pair = inner.next_or("expected a branch target");
        let otherwise_pair = inner.next_or("expected a branch target");

        let condition = self.parse_existing_local_of_ty(local_pair, Type::bool(), builder)?;
        let if_true = self.parse_block_target(if_pair, builder)?;
        let otherwise = self.parse_block_target(otherwise_pair, builder)?;

        builder.append().condbr(condition, if_true, otherwise, info);

        Ok(())
    }

    fn parse_unreachable(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::unreachable));

        builder
            .append()
            .unreachable(pair_into_info(pair, self.filename, None));

        Ok(())
    }

    fn parse_ret(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::ret));

        let info = pair_into_info(pair.clone(), self.filename, None);
        let as_span = pair.as_span();
        let mut inner = pair.into_inner();

        match inner.next() {
            Some(operand) => {
                let operand_span = operand.as_span();
                let val = self.parse_operand(operand, builder)?;

                if builder.current_signature().is_void() {
                    return Err(message_into_err(
                        operand_span,
                        "cannot return value from 'void' function",
                    ));
                }

                builder.append().ret_val(val, info);
            }
            None => {
                if !builder.current_signature().is_void() {
                    return Err(message_into_err(
                        as_span,
                        "must return value from non-'void' function",
                    ));
                }

                builder.append().ret_void(info);
            }
        }

        Ok(())
    }

    fn parse_binary_bitwise(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::binary_bitwise));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let opc = inner.next_or("expected bitwise_binary opcode").as_str();

        let (name, info) = self.parse_result(result, builder)?;
        let (lhs, rhs) = self.parse_existing_bitwise_binary_ops(&mut inner, builder)?;
        let ib = self.append_val(builder, name);

        match opc {
            "and" => ib.and(lhs, rhs, info),
            "or" => ib.or(lhs, rhs, info),
            "xor" => ib.xor(lhs, rhs, info),
            "shl" => ib.shl(lhs, rhs, info),
            "ashr" => ib.ashr(lhs, rhs, info),
            "lshr" => ib.lshr(lhs, rhs, info),
            _ => unreachable!(),
        };

        Ok(())
    }

    fn parse_binary_int(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::binary_int));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let opc = inner.next_or("expected bitwise_binary opcode").as_str();

        let (name, info) = self.parse_result(result, builder)?;
        let (lhs, rhs) = self.parse_existing_integer_binary_ops(&mut inner, builder)?;
        let ib = self.append_val(builder, name);

        match opc {
            "iadd" => ib.iadd(lhs, rhs, info),
            "isub" => ib.isub(lhs, rhs, info),
            "imul" => ib.imul(lhs, rhs, info),
            "sdiv" => ib.sdiv(lhs, rhs, info),
            "udiv" => ib.udiv(lhs, rhs, info),
            "srem" => ib.srem(lhs, rhs, info),
            "urem" => ib.urem(lhs, rhs, info),
            _ => unreachable!(),
        };

        Ok(())
    }

    fn parse_fneg(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::fneg));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected float_ty");
        let operand = inner.next_or("expected operand");

        if !matches!(ty_pair.as_rule(), Rule::float_ty) {
            return Err(message_into_err(
                ty_pair.as_span(),
                "expected floating-point type",
            ));
        }

        let (name, info) = self.parse_result(result, builder)?;
        let ty = self.parse_float_ty(ty_pair)?;
        let operand = self.parse_existing_local_of_ty(operand, ty, builder)?;

        self.append_val(builder, name).fneg(operand, info);

        Ok(())
    }

    fn parse_binary_float(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::binary_int));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let opc = inner.next_or("expected bitwise_binary opcode").as_str();

        let (name, info) = self.parse_result(result, builder)?;
        let (lhs, rhs) = self.parse_existing_float_binary_ops(&mut inner, builder)?;
        let ib = self.append_val(builder, name);

        match opc {
            "fadd" => ib.fadd(lhs, rhs, info),
            "fsub" => ib.fsub(lhs, rhs, info),
            "fmul" => ib.fmul(lhs, rhs, info),
            "fdiv" => ib.fdiv(lhs, rhs, info),
            "frem" => ib.frem(lhs, rhs, info),
            _ => unreachable!(),
        };

        Ok(())
    }

    fn parse_alloca(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::alloca));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected type");

        let (name, info) = self.parse_result(result, builder)?;
        let ty = self.parse_ty(ty_pair, builder.type_pool_mut())?;

        self.append_val(builder, name).alloca(ty, info);

        Ok(())
    }

    fn parse_load(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::load));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected type");
        let _ = inner.next_or("expected ptr");
        let val_pair = inner.next_or("expected value");

        let (name, info) = self.parse_result(result, builder)?;
        let ty = self.parse_ty(ty_pair, builder.type_pool_mut())?;
        let operand = self.parse_existing_local_of_ty(val_pair, Type::ptr(), builder)?;

        self.append_val(builder, name).load(ty, operand, info);

        Ok(())
    }

    fn parse_store(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::store));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let operand = inner.next_or("expected operand");
        let _ = inner.next_or("expected ptr");
        let val_pair = inner.next_or("expected value");

        let (name, info) = self.parse_result(result, builder)?;
        let operand = self.parse_operand(operand, builder)?;
        let ptr = self.parse_existing_local_of_ty(val_pair, Type::ptr(), builder)?;

        self.append_val(builder, name).store(operand, ptr, info);

        Ok(())
    }

    fn parse_offset(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::offset));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected ty");
        let _ = inner.next_or("expected ptr");
        let base_pair = inner.next_or("expected value");
        let int_ty = inner.next_or("expected int_ty");
        let offset_pair = inner.next_or("expected local");

        let (name, info) = self.parse_result(result, builder)?;
        let ty = self.parse_ty(ty_pair, builder.type_pool_mut())?;
        let offset_ty = self.parse_int_ty(int_ty)?;
        let base = self.parse_existing_local_of_ty(base_pair, Type::ptr(), builder)?;
        let offset = self.parse_existing_local_of_ty(offset_pair, offset_ty, builder)?;

        self.append_val(builder, name)
            .offset(ty, base, offset, info);

        Ok(())
    }

    fn agg_ty_properties(agg: Type, idx: u64, pool: &TypePool) -> (bool, Type) {
        match agg.unpack() {
            UType::Struct(ty) => {
                let members = ty.members(pool);
                let expected = members.get(idx as usize).copied();

                (expected.is_some(), expected.unwrap_or_else(Type::reserved))
            }
            UType::Array(ty) => {
                let element = ty.element(pool);
                let len = ty.len(pool);

                (idx < len, element)
            }
            _ => unreachable!(),
        }
    }

    fn check_agg_within_bounds(in_bounds: bool, idx_span: Span<'_>) -> ParseResult<()> {
        if !in_bounds {
            return Err(message_into_err(
                idx_span,
                "index out of bounds for aggregate",
            ));
        }

        Ok(())
    }

    fn check_agg_correct_ty(
        expected: Type,
        got: Type,
        idx_span: Span<'_>,
        pool: &TypePool,
    ) -> ParseResult<()> {
        if expected != got {
            let expected = stringify_ty(pool, expected);
            let got = stringify_ty(pool, got);

            return Err(string_into_err(
                idx_span,
                format!("incorrect extract ty, expected '{expected}' but got '{got}'"),
            ));
        }

        Ok(())
    }

    fn check_agg_operation_types(
        agg: Type,
        got: Type,
        idx: u64,
        idx_span: Span<'_>,
        builder: &FuncBuilder<'_>,
    ) -> ParseResult<()> {
        let (in_bounds, expected) = Self::agg_ty_properties(agg, idx, builder.type_pool());

        Self::check_agg_within_bounds(in_bounds, idx_span)?;
        Self::check_agg_correct_ty(expected, got, idx_span, builder.type_pool())?;

        Ok(())
    }

    fn parse_extract(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::extract));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let out_ty_pair = inner.next_or("expected ty");
        let agg_ty_pair = inner.next_or("expected struct_ty or array_ty");
        let agg_pair = inner.next_or("expected local");
        let idx_pair = inner.next_or("expected int constant");
        let idx_span = idx_pair.as_span();

        let (name, info) = self.parse_result(result, builder)?;
        let out_ty = self.parse_ty(out_ty_pair, builder.type_pool_mut())?;
        let agg_ty = self.parse_array_or_struct_ty(agg_ty_pair, builder.type_pool_mut())?;
        let agg = self.parse_existing_local_of_ty(agg_pair, agg_ty, builder)?;
        let idx = self.parse_int_lit(64, idx_pair)?;

        Self::check_agg_operation_types(agg_ty, out_ty, idx, idx_span, builder)?;

        self.append_val(builder, name)
            .extract(out_ty, agg, idx, info);

        Ok(())
    }

    fn parse_insert(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::insert));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let agg_ty_pair = inner.next_or("expected struct_ty or array_ty");
        let agg_pair = inner.next_or("expected local");
        let operand_pair = inner.next_or("expected operand");
        let idx_pair = inner.next_or("expected int constant");
        let idx_span = idx_pair.as_span();

        let (name, info) = self.parse_result(result, builder)?;
        let agg_ty = self.parse_array_or_struct_ty(agg_ty_pair, builder.type_pool_mut())?;
        let agg = self.parse_existing_local_of_ty(agg_pair, agg_ty, builder)?;
        let to_insert = self.parse_operand(operand_pair, builder)?;
        let idx = self.parse_int_lit(64, idx_pair)?;

        Self::check_agg_operation_types(agg_ty, builder.ty(to_insert), idx, idx_span, builder)?;

        self.append_val(builder, name)
            .insert(agg, to_insert, idx, info);

        Ok(())
    }

    fn parse_elemptr(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::elemptr));

        let mut inner = pair.into_inner();
        let result = inner.next_or("expected result");
        let agg_ty_pair = inner.next_or("expected struct_ty or array_ty");
        let _ = inner.next_or("expected ptr_ty");
        let base_pair = inner.next_or("expected local");
        let idx_pair = inner.next_or("expected int constant");
        let idx_span = idx_pair.as_span();

        let (name, info) = self.parse_result(result, builder)?;
        let agg_ty = self.parse_array_or_struct_ty(agg_ty_pair, builder.type_pool_mut())?;
        let base = self.parse_existing_local_of_ty(base_pair, Type::ptr(), builder)?;
        let idx = self.parse_int_lit(64, idx_pair)?;

        let (in_bounds, _) = Self::agg_ty_properties(agg_ty, idx, builder.type_pool());

        Self::check_agg_within_bounds(in_bounds, idx_span)?;

        self.append_val(builder, name)
            .elemptr(agg_ty, base, idx, info);

        Ok(())
    }

    fn parse_int_conv(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::int_conv));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let opcode = inner.next_or("expected opcode");
        let into_int_ty_pair = inner.next_or("expected int_ty");
        let from_int_ty_pair = inner.next_or("expected int_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_int_ty(into_int_ty_pair.clone())?;
        let from = self.parse_int_ty(from_int_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, from, builder)?;

        let builder = self.append_val(builder, name);

        match opcode.as_str() {
            "sext" => {
                if into.unwrap_int().width() <= from.unwrap_int().width() {
                    return Err(message_into_err(
                        into_int_ty_pair.as_span(),
                        "'sext' result type must be larger than input type",
                    ));
                }

                builder.sext(into, from_val, info);
            }
            "zext" => {
                if into.unwrap_int().width() <= from.unwrap_int().width() {
                    return Err(message_into_err(
                        into_int_ty_pair.as_span(),
                        "'zext' result type must be larger than input type",
                    ));
                }

                builder.zext(into, from_val, info);
            }
            "trunc" => {
                if into.unwrap_int().width() >= from.unwrap_int().width() {
                    return Err(message_into_err(
                        into_int_ty_pair.as_span(),
                        "'trunc' result type must be smaller than input type",
                    ));
                }

                builder.trunc(into, from_val, info);
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn parse_itob(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::itob));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let _ = inner.next_or("expected bool ty");
        let from_int_ty_pair = inner.next_or("expected int_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let from = self.parse_int_ty(from_int_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, from, builder)?;

        self.append_val(builder, name).itob(from_val, info);

        Ok(())
    }

    fn parse_btoi(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::btoi));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let into_int_ty_pair = inner.next_or("expected bool ty");
        let _ = inner.next_or("expected bool_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_int_ty(into_int_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, Type::bool(), builder)?;

        self.append_val(builder, name).btoi(into, from_val, info);

        Ok(())
    }

    fn parse_int_to_float(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::int_to_float));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let opcode = inner.next_or("expected opcode");
        let into_float_ty_pair = inner.next_or("expected float_ty");
        let from_int_ty_pair = inner.next_or("expected int_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_float_ty(into_float_ty_pair)?;
        let from = self.parse_int_ty(from_int_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, from, builder)?;

        let builder = self.append_val(builder, name);

        match opcode.as_str() {
            "sitof" => builder.sitof(into, from_val, info),
            "uitof" => builder.uitof(into, from_val, info),
            _ => unreachable!(),
        };

        Ok(())
    }

    fn parse_float_to_int(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::float_to_int));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let opcode = inner.next_or("expected opcode");
        let into_int_ty_pair = inner.next_or("expected int_ty");
        let from_float_ty_pair = inner.next_or("expected float_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_int_ty(into_int_ty_pair)?;
        let from = self.parse_float_ty(from_float_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, from, builder)?;

        let builder = self.append_val(builder, name);

        match opcode.as_str() {
            "ftosi" => builder.ftosi(into, from_val, info),
            "ftoui" => builder.ftoui(into, from_val, info),
            _ => unreachable!(),
        };

        Ok(())
    }

    fn parse_float_conv(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::float_conv));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let opcode = inner.next_or("expected opcode");
        let into_ty_pair = inner.next_or("expected float_ty");
        let from_ty_pair = inner.next_or("expected float_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_float_ty(into_ty_pair.clone())?;
        let from = self.parse_float_ty(from_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, from, builder)?;

        let builder = self.append_val(builder, name);

        match opcode.as_str() {
            "fext" => {
                if into.unwrap_float().format() as u32 <= from.unwrap_int().width() {
                    return Err(message_into_err(
                        into_ty_pair.as_span(),
                        "'fext' result type must be larger than input type",
                    ));
                }

                builder.sext(into, from_val, info);
            }
            "ftrunc" => {
                if into.unwrap_float().format() as u32 >= from.unwrap_int().width() {
                    return Err(message_into_err(
                        into_ty_pair.as_span(),
                        "'ftrunc' result type must be smaller than input type",
                    ));
                }

                builder.zext(into, from_val, info);
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn parse_itop(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::itop));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let _ = inner.next_or("expected ptr_ty");
        let from_int_ty_pair = inner.next_or("expected int_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let from = self.parse_int_ty(from_int_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, from, builder)?;

        self.append_val(builder, name).itop(from_val, info);

        Ok(())
    }

    fn parse_ptoi(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::ptoi));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let into_int_ty_pair = inner.next_or("expected bool ty");
        let _ = inner.next_or("expected ptr_ty");
        let from_local = inner.next_or("expected local");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_int_ty(into_int_ty_pair)?;
        let from_val = self.parse_existing_local_of_ty(from_local, Type::ptr(), builder)?;

        self.append_val(builder, name).ptoi(into, from_val, info);

        Ok(())
    }

    fn parse_iconst(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::iconst));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected int_ty");
        let literal = inner.next_or("expected int_literal");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_int_ty(ty_pair)?;
        let val = self.parse_int_lit(into.unwrap_int().width(), literal)?;

        self.append_val(builder, name).iconst(into, val, info);

        Ok(())
    }

    fn parse_fconst(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::fconst));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected float_ty");
        let literal = inner.next_or("expected float_literal");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let into = self.parse_float_ty(ty_pair)?;
        let val = self.parse_float_lit(into.unwrap_float().format(), literal)?;

        self.append_val(builder, name).fconst_raw(into, val, info);

        Ok(())
    }

    fn parse_bconst(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::bconst));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let _ = inner.next_or("expected bool_ty");
        let literal = inner.next_or("expected bool_literal");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let val = self.parse_bool_lit(literal)?;

        self.append_val(builder, name).bconst(val, info);

        Ok(())
    }

    fn parse_undef(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::undef));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected ty");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let ty = self.parse_ty(ty_pair, builder.type_pool_mut())?;

        self.append_val(builder, name).undef(ty, info);

        Ok(())
    }

    fn parse_null(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::null));

        let mut inner = pair.into_inner();
        let result_pair = inner.next_or("expected result");
        let ty_pair = inner.next_or("expected ty");

        let (name, info) = self.parse_result(result_pair, builder)?;
        let ty = self.parse_ty(ty_pair, builder.type_pool_mut())?;

        self.append_val(builder, name).null(ty, info);

        Ok(())
    }

    fn parse_globaladdr(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        debug_assert!(matches!(pair.as_rule(), Rule::globaladdr));

        let _ = builder;

        todo!()
    }

    fn parse_operand(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Value> {
        debug_assert!(matches!(pair.as_rule(), Rule::operand));

        let mut pairs = pair.into_inner();
        let ty_pair = pairs.next_or("expected type");
        let ty = self.parse_ty(ty_pair, builder.type_pool_mut())?;
        let name_pair = pairs.next_or("expected name with type");

        self.parse_existing_local_of_ty(name_pair, ty, builder)
    }

    fn parse_block_target(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<BlockWithParams> {
        debug_assert!(matches!(pair.as_rule(), Rule::block_target));

        let mut inner = pair.into_inner();
        let name_pair = inner.next_or("expected ident");
        let name = name_pair.as_str();

        debug_assert!(matches!(name_pair.as_rule(), Rule::ident));

        let bb = match builder.find_block(name) {
            Some(bb) => bb,
            None => {
                return Err(message_into_err(name_pair.as_span(), "unknown basic block"));
            }
        };

        let args = match inner.next() {
            Some(args_with_ty) => self.parse_block_arg_with_types(bb, args_with_ty, builder)?,
            None if builder.block_params(bb).is_empty() => vec![],
            None => {
                return Err(message_into_err(
                    name_pair.as_span(),
                    "expected block arguments",
                ));
            }
        };

        Ok(BlockWithParams::from_vec(bb, args))
    }

    fn parse_existing_bitwise_binary_ops(
        &mut self,
        pairs: &mut Pairs<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(Value, Value)> {
        let (lhs, rhs) = self.parse_existing_ty_binary_ops(pairs, builder)?;

        for (val, span) in [lhs, rhs] {
            let ty = builder.ty(val);

            if !ty.is_bool_or_int() {
                let msg = format!(
                    "unexpected type for value, expected 'bool' or integer but got '{}'",
                    stringify_ty(builder.type_pool(), ty)
                );

                return Err(string_into_err(span, msg));
            }
        }

        Ok((lhs.0, rhs.0))
    }

    fn parse_existing_integer_binary_ops(
        &mut self,
        pairs: &mut Pairs<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(Value, Value)> {
        let (lhs, rhs) = self.parse_existing_ty_binary_ops(pairs, builder)?;

        for (val, span) in [lhs, rhs] {
            let ty = builder.ty(val);

            if !ty.is_int() {
                let msg = format!(
                    "unexpected type for value, expected integer but got '{}'",
                    stringify_ty(builder.type_pool(), ty)
                );

                return Err(string_into_err(span, msg));
            }
        }

        Ok((lhs.0, rhs.0))
    }

    fn parse_existing_float_binary_ops(
        &mut self,
        pairs: &mut Pairs<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(Value, Value)> {
        let (lhs, rhs) = self.parse_existing_ty_binary_ops(pairs, builder)?;

        for (val, span) in [lhs, rhs] {
            let ty = builder.ty(val);

            if !ty.is_float() {
                let msg = format!(
                    "unexpected type for value, expected float but got '{}'",
                    stringify_ty(builder.type_pool(), ty)
                );

                return Err(string_into_err(span, msg));
            }
        }

        Ok((lhs.0, rhs.0))
    }

    fn parse_existing_ty_binary_ops<'a>(
        &mut self,
        pairs: &mut Pairs<'a, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<((Value, Span<'a>), (Value, Span<'a>))> {
        let next = pairs.next_or("expected ty");

        let ty = match next.as_rule() {
            Rule::bool_ty => Type::bool(),
            Rule::ptr_ty => Type::ptr(),
            Rule::float_ty => self.parse_float_ty(next)?,
            Rule::int_ty => self.parse_int_ty(next)?,
            _ => unreachable!(),
        };

        let mut binary = pairs.next_or("expecting binary_operands").into_inner();
        let lhs_pair = binary.next_or("expected lhs");
        let rhs_pair = binary.next_or("expected lhs");
        let lhs_span = lhs_pair.as_span();
        let rhs_span = rhs_pair.as_span();
        let lhs = self.parse_existing_local_of_ty(lhs_pair, ty, builder)?;
        let rhs = self.parse_existing_local_of_ty(rhs_pair, ty, builder)?;

        Ok(((lhs, lhs_span), (rhs, rhs_span)))
    }

    fn parse_existing_local_of_ty(
        &mut self,
        pair: Pair<'_, Rule>,
        ty: Type,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Value> {
        let name_span = pair.as_span();
        let val = self.parse_existing_local(pair, builder)?;

        if ty != builder.ty(val) {
            let expected = stringify_ty(builder.type_pool(), ty);
            let got = stringify_ty(builder.type_pool(), builder.ty(val));
            let err = format!(
                "mismatched types for value '{}', expected '{}' but got '{}'",
                name_span.as_str(),
                expected,
                got
            );

            Err(string_into_err(name_span, err))
        } else {
            Ok(val)
        }
    }

    fn parse_result(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(LocalIdent, DebugInfo)> {
        debug_assert!(matches!(pair.as_rule(), Rule::result));

        let mut pairs = pair.into_inner();
        let local = pairs.next_or("expected local");

        self.parse_new_local(local, builder)
    }

    fn parse_optional_result(
        &mut self,
        pair: &mut Pairs<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Option<(LocalIdent, DebugInfo)>> {
        match pair.peek().map(|p| p.as_rule()) {
            Some(Rule::result) => {
                let result = pair.next_or("expected result");

                Ok(Some(self.parse_result(result, builder)?))
            }
            _ => Ok(None),
        }
    }

    // parses a local identifier into a string.
    fn parse_raw_local(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(LocalIdent, DebugInfo)> {
        debug_assert!(matches!(pair.as_rule(), Rule::local));

        // skip the %
        let real: String = pair.as_str().chars().skip(1).collect();

        match real.parse::<u32>() {
            Ok(num) => {
                let info = pair_into_info(pair, self.filename, None);

                Ok((LocalIdent::Num(num), info))
            }
            Err(_) => {
                let key = builder.string_pool_mut().insert(&real);
                let info = pair_into_info(pair, self.filename, Some(key));

                Ok((LocalIdent::Name(key), info))
            }
        }
    }

    // preprocesses block param idents so that we can just get them registered for now
    // (so that other code can't use them too), but we dont check that the number is actually
    // in order yet. we do that when we come back to the block after pre-processing
    fn preprocess_block_param_local(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(LocalIdent, DebugInfo)> {
        let span = pair.as_span();
        let (local, debug) = self.parse_raw_local(pair, builder)?;

        // we intentionally skip the numbering, but we also return the pair so
        // that it can be properly verified for numbering later.
        if self.resolver.contains_key(&local) {
            return Err(string_into_err(
                span,
                format!("duplicate value '{}'", span.as_str()),
            ));
        }

        Ok((local, debug))
    }

    fn verify_block_param_local(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<()> {
        let span = pair.as_span();
        let (local, _) = self.parse_raw_local(pair, builder)?;

        if let LocalIdent::Num(num) = local {
            if num != self.next {
                let msg = format!(
                    "block param should be numbered '%{}' but got '%{num}'",
                    self.next
                );
                let err = string_into_err(span, msg);

                return Err(err);
            }

            self.next += 1;
        }

        Ok(())
    }

    // parses a local that shouldn't have been seen before in the current function. this is for
    // result names, block parma names, etc
    fn parse_new_local(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<(LocalIdent, DebugInfo)> {
        let span = pair.as_span();
        let (local, debug) = self.parse_raw_local(pair, builder)?;

        if self.resolver.contains_key(&local) {
            return Err(string_into_err(
                span,
                format!("duplicate value '{}'", span.as_str()),
            ));
        }

        if let LocalIdent::Num(num) = local {
            if num != self.next {
                let msg = format!("value should be numbered '%{}' but got '%{num}'", self.next);
                let err = string_into_err(span, msg);

                return Err(err);
            }

            self.next += 1;
        }

        Ok((local, debug))
    }

    fn parse_existing_local(
        &mut self,
        pair: Pair<'_, Rule>,
        builder: &mut FuncBuilder<'_>,
    ) -> ParseResult<Value> {
        let span = pair.as_span();
        let (local, _) = self.parse_raw_local(pair, builder)?;

        match self.resolver.get(&local) {
            Some(val) => Ok(*val),
            None => Err(string_into_err(
                span,
                format!("unknown value '{}'", span.as_str()),
            )),
        }
    }

    fn parse_global(&mut self, pair: Pair<'_, Rule>) -> ParseResult<String> {
        debug_assert!(matches!(pair.as_rule(), Rule::global));

        // skip the @
        Ok(pair.as_str().chars().skip(1).collect())
    }

    fn parse_array_or_struct_ty(
        &mut self,
        pair: Pair<'_, Rule>,
        pool: &mut TypePool,
    ) -> ParseResult<Type> {
        match pair.as_rule() {
            Rule::array_ty => self.parse_array_ty(pair, pool),
            Rule::struct_ty => self.parse_struct_ty(pair, pool),
            _ => unreachable!(),
        }
    }

    fn parse_ty_or_void(
        &mut self,
        pair: Pair<'_, Rule>,
        pool: &mut TypePool,
    ) -> ParseResult<Option<Type>> {
        debug_assert!(matches!(pair.as_rule(), Rule::ty_or_void));

        if pair.as_str() == "void" {
            Ok(None)
        } else {
            let ty_pair = pair.into_inner().next_or("expected type");
            let ty = self.parse_ty(ty_pair, pool)?;

            Ok(Some(ty))
        }
    }

    fn parse_ty_list(
        &mut self,
        pair: Pair<'_, Rule>,
        pool: &mut TypePool,
    ) -> ParseResult<Vec<Type>> {
        debug_assert!(matches!(pair.as_rule(), Rule::ty_list));

        pair // collect has a version returning Result<_, _>
            .into_inner()
            .map(|pair| self.parse_ty(pair, pool))
            .collect()
    }

    fn parse_int_ty(&mut self, pair: Pair<'_, Rule>) -> ParseResult<Type> {
        debug_assert!(matches!(pair.as_rule(), Rule::int_ty));

        let width = u32::from_str(&pair.as_str()[1..])?;
        let ty = Type::int(width);

        Ok(ty)
    }

    fn parse_float_ty(&mut self, pair: Pair<'_, Rule>) -> ParseResult<Type> {
        debug_assert!(matches!(pair.as_rule(), Rule::float_ty));

        match u32::from_str(&pair.as_str()[1..]) {
            Ok(32) => Ok(Type::f32()),
            Ok(64) => Ok(Type::f64()),
            Err(e) => Err(Box::new(e).into()),
            _ => unreachable!(),
        }
    }

    fn parse_array_ty(&mut self, pair: Pair<'_, Rule>, pool: &mut TypePool) -> ParseResult<Type> {
        debug_assert!(matches!(pair.as_rule(), Rule::array_ty));

        let mut pairs = pair.into_inner();
        let ty = pairs.next_or("expected ty for array");
        let lit = pairs.next_or("expected int literal for array");
        let elem_ty = self.parse_ty(ty, pool)?;
        let len = self.parse_int_lit(64, lit)?;

        Ok(Type::array(pool, elem_ty, len))
    }

    fn parse_struct_ty(&mut self, pair: Pair<'_, Rule>, pool: &mut TypePool) -> ParseResult<Type> {
        debug_assert!(matches!(pair.as_rule(), Rule::struct_ty));

        let mut pairs = pair.into_inner();
        let list = pairs.next_or("expected ty list for struct");
        let tys = self.parse_ty_list(list, pool)?;

        Ok(Type::structure(pool, &tys))
    }

    fn parse_ty(&mut self, pair: Pair<'_, Rule>, pool: &mut TypePool) -> ParseResult<Type> {
        debug_assert!(matches!(pair.as_rule(), Rule::ty));

        let inner = pair.into_inner().next_or("expected type");

        match inner.as_rule() {
            Rule::int_ty => self.parse_int_ty(inner),
            Rule::float_ty => self.parse_float_ty(inner),
            Rule::bool_ty => Ok(Type::bool()),
            Rule::ptr_ty => Ok(Type::ptr()),
            Rule::array_ty => self.parse_array_ty(inner, pool),
            Rule::struct_ty => self.parse_struct_ty(inner, pool),
            _ => unreachable!(),
        }
    }

    fn parse_int_lit(&mut self, width: u32, lit: Pair<'_, Rule>) -> ParseResult<u64> {
        debug_assert!(matches!(lit.as_rule(), Rule::int_literal));

        let s = lit.as_str();

        if s.starts_with('-') {
            match width {
                8 => Ok(i8::from_str(s)? as u8 as u64),
                16 => Ok(i16::from_str(s)? as u16 as u64),
                32 => Ok(i32::from_str(s)? as u32 as u64),
                64 => Ok(i64::from_str(s)? as u64),
                _ => unreachable!(),
            }
        } else if s.starts_with("0b") {
            match width {
                8 => Ok(u8::from_str_radix(s, 2)? as u64),
                16 => Ok(u16::from_str_radix(s, 2)? as u64),
                32 => Ok(u32::from_str_radix(s, 2)? as u64),
                64 => Ok(u64::from_str_radix(s, 2)?),
                _ => unreachable!(),
            }
        } else if s.starts_with("0o") {
            match width {
                8 => Ok(u8::from_str_radix(s, 8)? as u64),
                16 => Ok(u16::from_str_radix(s, 8)? as u64),
                32 => Ok(u32::from_str_radix(s, 8)? as u64),
                64 => Ok(u64::from_str_radix(s, 8)?),
                _ => unreachable!(),
            }
        } else if s.starts_with("0x") {
            match width {
                8 => Ok(u8::from_str_radix(s, 16)? as u64),
                16 => Ok(u16::from_str_radix(s, 16)? as u64),
                32 => Ok(u32::from_str_radix(s, 16)? as u64),
                64 => Ok(u64::from_str_radix(s, 16)?),
                _ => unreachable!(),
            }
        } else {
            debug_assert!(s.chars().all(|c| c.is_ascii_digit()));

            match width {
                8 => Ok(u8::from_str(s)? as u64),
                16 => Ok(u16::from_str(s)? as u64),
                32 => Ok(u32::from_str(s)? as u64),
                64 => Ok(u64::from_str(s)?),
                _ => unreachable!(),
            }
        }
    }

    fn parse_float_lit(&mut self, format: FloatFormat, lit: Pair<'_, Rule>) -> ParseResult<u64> {
        debug_assert!(matches!(lit.as_rule(), Rule::float_literal));

        match lit.as_str() {
            "NaN" => match format {
                FloatFormat::Single => Ok(f32::NAN.to_bits() as u64),
                FloatFormat::Double => Ok(f64::NAN.to_bits()),
            },
            s if s.starts_with("0xfp") => match format {
                FloatFormat::Single => {
                    Ok(u32::from_str_radix(s.strip_prefix("0xfp").unwrap(), 16)? as u64)
                }
                FloatFormat::Double => {
                    Ok(u64::from_str_radix(s.strip_prefix("0xfp").unwrap(), 16)?)
                }
            },
            s => {
                let raw = match format {
                    FloatFormat::Single => f32::from_str(s).map(|f| f.to_bits() as u64),
                    FloatFormat::Double => f64::from_str(s).map(|f| f.to_bits()),
                };

                raw.map_err(|err| {
                    string_into_err(lit.as_span(), format!("unable to parse float: '{err}'"))
                })
            }
        }
    }

    fn parse_bool_lit(&mut self, lit: Pair<'_, Rule>) -> ParseResult<bool> {
        debug_assert!(matches!(lit.as_rule(), Rule::bool_literal));

        match lit.as_str() {
            "true" => Ok(true),
            "false" => Ok(false),
            _ => unreachable!(),
        }
    }

    fn append_val<'f, 'p>(
        &'p mut self,
        builder: &'f mut FuncBuilder<'_>,
        ident: LocalIdent,
    ) -> ResolveAppendBuilder<'f, 'p> {
        ResolveAppendBuilder {
            ident,
            builder: builder.append(),
            parser: self,
        }
    }
}

/// Parses a SIR source file into a module, or returns the first
/// error that occurred while parsing.
///
/// Multiple errors are not collected for performance reasons, this is
/// an IR meant to be used by compiler people.
pub fn parse_sir(filename: &str, source: &str) -> Result<Module, Box<dyn Error>> {
    let result = generated::SIRReader::parse(Rule::sir, source)?;

    SIRParser::parse(filename, result)
}
