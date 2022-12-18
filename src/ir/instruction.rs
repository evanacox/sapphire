//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{Block, EntityStorage, FloatFormat, Func, Int, Sig, Type, Value};
use slotmap::{Key, KeyData};
use std::iter;
use std::slice;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// This holds both the opcode of a given instruction and all the state
/// that makes up that specific instruction.
///
/// While each instruction may have wildly different actual data, they all
/// are stored in the same table and all inside the same `InstructionData` type.
#[repr(u32)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum InstData {
    /// `call T @function(args...)`, models a direct call to a known function.
    Call(CallInst),
    /// `call T %var(args...)`, models an indirect call through a pointer.
    IndirectCall(IndirectCallInst),
    /// `icmp op T %a, %b`, models an integer comparison
    ICmp(ICmpInst),
    /// `fcmp op T %a, %b`, models a floating-point comparison
    FCmp(FCmpInst),
    /// `sel bool %cond, T %a, T %b`, models a ternary-like instruction
    Sel(CondBrInst),
    /// `br block`, models an unconditional branch
    Br(BrInst),
    /// `condbr bool %cond, if block1, else block2`, models a conditional branch between two blocks
    CondBr(CondBrInst),
    /// `switch T %val, otherwise block, [ (T %const1 block1), (T %const1 block1) ]
    Switch(SwitchInst),
    Unreachable(UnreachableInst),
    Ret(RetInst),
    And(CommutativeArithInst),
    Or(CommutativeArithInst),
    Xor(CommutativeArithInst),
    Shl(ArithInst),
    AShr(ArithInst),
    LShr(ArithInst),
    IAdd(CommutativeArithInst),
    ISub(ArithInst),
    IMul(CommutativeArithInst),
    SDiv(ArithInst),
    UDiv(ArithInst),
    SRem(ArithInst),
    URem(ArithInst),
    FNeg(FloatUnaryInst),
    FAdd(ArithInst),
    FSub(ArithInst),
    FMul(ArithInst),
    FDiv(ArithInst),
    FRem(ArithInst),
    Alloca,
    Load,
    Store,
    Offset,
    Extract,
    Insert,
    Elemptr,
    Sext(CastInst),
    Zext(CastInst),
    Trunc(CastInst),
    IToB(CastInst),
    BToI(CastInst),
    SIToF(CastInst),
    UIToF(CastInst),
    FToSI(CastInst),
    FToUI(CastInst),
    IToP(CastInst),
    PToI(CastInst),
    IConst(IConstInst),
    FConst(FConstInst),
    BConst(BConstInst),
    Undef(UndefConstInst),
    Null(NullConstInst),
    GlobalAddr(GlobalAddrInst),
}

/// These are the properties that any transform or analysis pass needs to be
/// able to observe for any given instruction in any block.
///
/// Any instruction's data can be passed as a `&dyn Instruction`, because every
/// valid opcode has at least an implementation for `Instruction`.
pub trait Instruction {
    /// Gets any operands that the instruction operates on.
    ///
    /// Note that this may be an empty array, it is not safe to assume that
    /// there will be at least one operand.
    fn operands(&self) -> &[Value];

    /// Gets the type of the instruction's result after it has been evaluated.  
    ///
    /// Not all instructions will have one of these, e.g. terminators, `call void`s
    /// and `store`s do not evaluate to anything.
    fn result_ty(&self) -> Option<Type>;

    fn has_result(&self) -> bool {
        self.result_ty().is_none()
    }
}

/// Some instructions model binary operations, those instructions model this trait.
///
/// A valid assumption for any type implementing this trait is that the operands
/// returned by [`Instruction::operands`] has a length of exactly 2. However,
/// it is not valid to assume that any instruction implementing this follows the
/// same pattern as most arithmetic instructions (i.e. [`lhs`] and [`rhs`] do **not**
/// always have the same type, and [`Instruction::result_ty`] may be different from
/// the type of the operands).
pub trait BinaryInst: Instruction {
    /// Gets the left-hand operand of the instruction. For `inst T %a, %b`,
    /// this would be `%a`.
    fn lhs(&self) -> Value {
        self.operands()[0]
    }

    /// Gets the left-hand operand of the instruction. For `inst T %a, %b`,
    /// this would be `%b`.
    fn rhs(&self) -> Value {
        self.operands()[1]
    }

    /// Checks if the binary instruction follows the commutative property, i.e.
    /// whether it is safe to swap the operands while preserving the behavior.
    fn is_commutative(&self) -> bool;
}

/// Some instructions model unary operations, those instructions model this trait.
///
/// A valid assumption for any type implementing this trait is that the operands
/// returned by [`Instruction::operands`] has a length of exactly 1.
///
/// While most instructions implementing this are casts, not all of them are.
/// A few instructions (notably `fneg`) are unary but not casts.
pub trait UnaryInst: Instruction {
    fn operand(&self) -> Value {
        self.operands()[0]
    }
}

/// Models a terminator, i.e. the only instructions that are allowed at the end
/// of a basic block.
///
/// All terminators transfer control flow *somewhere* unless they end execution,
/// so users need to be able to query where control could be transferred to.
pub trait Terminator: Instruction {
    /// Gets the possible blocks where control could be transferred to
    /// once this instruction is executed.
    ///
    /// Note that this might be empty, see `unreachable` or `ret`.
    fn targets(&self) -> &[Block];

    #[doc(hidden)]
    fn __operands(&self) -> &[Value];
}

impl<T: Terminator> Instruction for T {
    fn operands(&self) -> &[Value] {
        self.__operands()
    }

    fn result_ty(&self) -> Option<Type> {
        None
    }
}

/// Models the different ways that integers values can be compared in SIR
/// using the `icmp` instruction.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum ICmpOp {
    /// `eq`, checks if the integers are (bitwise) equivalent
    EQ,
    /// `ne`, checks if the integers are (bitwise) not-equal
    NE,
    /// `sgt`, treats both integers as signed and checks if `a > b`
    SGT,
    /// `slt`, treats both integers as signed and checks if `a < b`
    SLT,
    /// `sge`, treats both integers as signed and checks if `a >= b`
    SGE,
    /// `sle`, treats both integers as signed and checks if `a <= b`
    SLE,
    /// `ugt`, treats both integers as unsigned and checks if `a > b`
    UGT,
    /// `ult`, treats both integers as unsigned and checks if `a < b`
    ULT,
    /// `uge`, treats both integers as unsigned and checks if `a >= b`
    UGE,
    /// `ule`, treats both integers as unsigned and checks if `a <= b`
    ULE,
}

/// Models a single `icmp` instruction.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ICmpInst {
    comparison: ICmpOp,
    operands: [Value; 2],
}

impl ICmpInst {
    fn new(dfg: &EntityStorage, comp: ICmpOp, lhs: Value, rhs: Value) -> Self {
        debug_assert_eq!(dfg.data(lhs).result_ty(), dfg.data(rhs).result_ty());
        debug_assert_eq!(
            dfg.data(lhs)
                .result_ty()
                .map(|ty| ty.is_int() || ty.is_bool()),
            Some(true)
        );

        Self {
            comparison: comp,
            operands: [lhs, rhs],
        }
    }

    pub fn op(&self) -> ICmpOp {
        self.comparison
    }
}

impl Instruction for ICmpInst {
    fn operands(&self) -> &[Value] {
        &self.operands
    }

    fn result_ty(&self) -> Option<Type> {
        Some(Type::bool())
    }
}

impl BinaryInst for ICmpInst {
    fn is_commutative(&self) -> bool {
        match self.op() {
            ICmpOp::EQ | ICmpOp::NE => true,
            _ => false,
        }
    }
}

/// Models the different ways that floating-point values can be
/// compared in SIR.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum FCmpOp {
    /// `uno`, "unordered." Checks if either operand is a `NaN`.
    UNO,
    /// `ord`, "ordered." Checks that both operands are not `NaN`s.
    ORD,
    /// `oeq`, "ordered and equal." Checks if the operands are ordered and `a == b`.
    OEQ,
    /// `one`, "ordered and not equal." Checks if the operands are ordered and `a != b`
    ONE,
    /// `ogt`, "ordered and greater-than." Checks if both operands are ordered and that `a > b`
    OGT,
    /// `olt`, "ordered and less-than." Checks if both operands are ordered and that `a < b`
    OLT,
    /// `oge`, "ordered and greater-than-or-equals." Checks if both operands are ordered and `a >= b`
    OGE,
    /// `ole`, "ordered and less-than-or-equals." Checks if both operands are ordered and `a <= b`
    OLE,
    /// `ueq`, "unordered and equal." Checks if the operands are unordered and `a == b`.
    UEQ,
    /// `une`, "unordered and not equal." Checks if the operands are unordered and `a != b`
    UNE,
    /// `ugt`, "unordered and greater-than." Checks if both operands are unordered and that `a > b`
    UGT,
    /// `olt`, "unordered and less-than." Checks if both operands are unordered and that `a < b`
    ULT,
    /// `uge`, "unordered and greater-than-or-equals." Checks if both operands are unordered and `a >= b`
    UGE,
    /// `ule`, "unordered and less-than-or-equals." Checks if both operands are unordered and `a <= b`
    ULE,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct FCmpInst {
    comparison: FCmpOp,
    operands: [Value; 2],
}

impl FCmpInst {
    fn new(_: &EntityStorage, comp: FCmpOp, lhs: Value, rhs: Value) -> Self {
        Self {
            comparison: comp,
            operands: [lhs, rhs],
        }
    }

    pub fn op(&self) -> FCmpOp {
        self.comparison
    }
}

impl Instruction for FCmpInst {
    fn operands(&self) -> &[Value] {
        &self.operands
    }

    fn result_ty(&self) -> Option<Type> {
        Some(Type::bool())
    }
}

impl BinaryInst for FCmpInst {
    fn is_commutative(&self) -> bool {
        match self.op() {
            FCmpOp::OEQ | FCmpOp::ONE | FCmpOp::UEQ | FCmpOp::UNE => true,
            _ => false,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct SelInst {
    operands: [Value; 3],
    output: Type,
}

impl SelInst {
    fn new(dfg: &EntityStorage, cond: Value, if_true: Value, otherwise: Value) -> Self {
        Self {
            operands: [cond, if_true, otherwise],
            output: dfg
                .data(if_true)
                .result_ty()
                .expect("`sel` operands must have types"),
        }
    }

    pub fn condition(&self) -> Value {
        self.operands[0]
    }

    pub fn if_true(&self) -> Value {
        self.operands[1]
    }

    pub fn if_false(&self) -> Value {
        self.operands[2]
    }
}

impl Instruction for SelInst {
    fn operands(&self) -> &[Value] {
        &self.operands
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.output)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct BrInst {
    target: Block,
}

impl BrInst {
    fn new(target: Block) -> Self {
        Self { target }
    }

    pub fn target(&self) -> Block {
        self.target
    }
}

impl Terminator for BrInst {
    fn targets(&self) -> &[Block] {
        slice::from_ref(&self.target)
    }

    fn __operands(&self) -> &[Value] {
        &[]
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct CondBrInst {
    operand: Value,
    targets: [Block; 2],
}

impl CondBrInst {
    fn new(cond: Value, if_true: Block, otherwise: Block) -> Self {
        Self {
            operand: cond,
            targets: [if_true, otherwise],
        }
    }

    pub fn condition(&self) -> Value {
        self.operand
    }

    pub fn true_branch(&self) -> Block {
        self.targets[0]
    }

    pub fn false_branch(&self) -> Block {
        self.targets[1]
    }
}

impl Terminator for CondBrInst {
    fn targets(&self) -> &[Block] {
        &self.targets
    }

    fn __operands(&self) -> &[Value] {
        slice::from_ref(&self.operand)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct SwitchInst {
    // blocks[0] stores the "else" block
    blocks: Vec<Block>,
    // operands[0] stores the value being switched on
    operands: Vec<Value>,
}

impl SwitchInst {
    fn new(_: &EntityStorage, operand: Value, otherwise: Block, pairs: &[(Value, Block)]) -> Self {
        let mut blocks = vec![otherwise];
        let mut operands = vec![operand];

        for (val, bb) in pairs {
            operands.push(*val);
            blocks.push(*bb);
        }

        Self { blocks, operands }
    }

    pub fn operand(&self) -> Value {
        self.operands[0]
    }

    pub fn otherwise(&self) -> Block {
        self.blocks[0]
    }

    pub fn pairs(&self) -> impl Iterator<Item = (Value, Block)> {
        iter::zip(self.operands.iter(), self.blocks.iter()).map(|(op, block)| (*op, *block))
    }
}

impl Terminator for SwitchInst {
    fn targets(&self) -> &[Block] {
        &self.blocks
    }

    fn __operands(&self) -> &[Value] {
        &self.operands
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct UnreachableInst(());

impl UnreachableInst {
    fn new() -> Self {
        Self(())
    }
}

impl Terminator for UnreachableInst {
    fn targets(&self) -> &[Block] {
        &[]
    }

    fn __operands(&self) -> &[Value] {
        &[]
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct RetInst {
    returning: Type,
    value: Value,
}

impl RetInst {
    fn new(dfg: &EntityStorage, val: Value) -> Self {
        Self {
            value: val,
            returning: dfg
                .data(val)
                .result_ty()
                .expect("cannot return instruction without a type"),
        }
    }
}

impl Terminator for RetInst {
    fn targets(&self) -> &[Block] {
        &[]
    }

    fn __operands(&self) -> &[Value] {
        slice::from_ref(&self.value)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct ArithmeticInst<const Commutative: bool> {
    output: Type,
    operands: [Value; 2],
}

impl<const C: bool> ArithmeticInst<C> {
    fn new(dfg: &EntityStorage, lhs: Value, rhs: Value) -> Self {
        Self {
            operands: [lhs, rhs],
            output: dfg
                .data(lhs)
                .result_ty()
                .expect("arithmetic instruction operand should have a type"),
        }
    }
}

impl<const C: bool> Instruction for ArithmeticInst<C> {
    fn operands(&self) -> &[Value] {
        &self.operands
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.output)
    }
}

impl<const C: bool> BinaryInst for ArithmeticInst<C> {
    fn is_commutative(&self) -> bool {
        C
    }
}

pub type CommutativeArithInst = ArithmeticInst<true>;

pub type ArithInst = ArithmeticInst<false>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct CastInst {
    output: Type,
    operand: Value,
}

impl CastInst {
    fn new(dfg: &EntityStorage, operand: Value) -> Self {
        Self {
            operand,
            output: dfg
                .data(operand)
                .result_ty()
                .expect("cast instruction operand should have a type"),
        }
    }
}

impl Instruction for CastInst {
    fn operands(&self) -> &[Value] {
        slice::from_ref(&self.operand)
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.output)
    }
}

impl UnaryInst for CastInst {}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct FloatUnaryInst {
    output: Type,
    operand: Value,
}

impl FloatUnaryInst {
    fn new(dfg: &EntityStorage, operand: Value) -> Self {
        Self {
            operand,
            output: dfg
                .data(operand)
                .result_ty()
                .expect("float unary instruction operand should have a type"),
        }
    }
}

impl Instruction for FloatUnaryInst {
    fn operands(&self) -> &[Value] {
        slice::from_ref(&self.operand)
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.output)
    }
}

impl UnaryInst for FloatUnaryInst {}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct CallInst {
    sig: Sig,
    output: Option<Type>, // compiler is combining the combining of `Option` and `Type` here
    operands: Vec<Value>,
}

impl CallInst {
    fn new(dfg: &EntityStorage, signature: Sig, callee: Func, args: &[Value]) -> Self {
        let mut vec = vec![Value::from(KeyData::from_ffi(callee.data().as_ffi()))];

        vec.extend_from_slice(args);

        Self {
            sig: signature,
            output: dfg.signature(signature).return_ty(),
            operands: vec,
        }
    }

    pub fn callee(&self) -> Func {
        // we take the underlying data of the first key and convert it
        // into a function key instead, since that's what it actually is
        Func::from(KeyData::from_ffi(self.operands[0].data().as_ffi()))
    }

    pub fn args(&self) -> &[Value] {
        &self.operands[1..]
    }
}

impl Instruction for CallInst {
    fn operands(&self) -> &[Value] {
        self.args()
    }

    fn result_ty(&self) -> Option<Type> {
        self.output
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct IndirectCallInst {
    sig: Sig,
    output: Option<Type>, // compiler is combining the combining of `Option` and `Type` here
    operands: Vec<Value>,
}

impl IndirectCallInst {
    fn new(dfg: &EntityStorage, signature: Sig, callee: Value, args: &[Value]) -> Self {
        let mut vec = vec![
            Value::from(KeyData::from_ffi(signature.data().as_ffi())),
            callee,
        ];

        vec.extend_from_slice(args);

        Self {
            sig: signature,
            operands: vec,
            output: dfg.signature(signature).return_ty(),
        }
    }

    pub fn callee(&self) -> Value {
        self.operands[0]
    }

    pub fn args(&self) -> &[Value] {
        &self.operands[1..]
    }
}

impl Instruction for IndirectCallInst {
    fn operands(&self) -> &[Value] {
        &self.operands
    }

    fn result_ty(&self) -> Option<Type> {
        self.output
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct IConstInst {
    constant: u64,
    mask: u64,
    ty: Type,
}

impl IConstInst {
    fn new(ty: Type, constant: u64) -> Self {
        Self {
            constant,
            ty,
            mask: ty.unwrap_int().mask(),
        }
    }

    pub fn value(&self) -> u64 {
        self.constant & self.mask
    }
}

impl Instruction for IConstInst {
    fn operands(&self) -> &[Value] {
        &[]
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.ty)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct FConstInst {
    constant: u64,
    mask: u64,
    ty: Type,
}

impl FConstInst {
    fn new(ty: Type, constant: u64) -> Self {
        Self {
            constant,
            ty,
            mask: match ty.unwrap_float().format() {
                FloatFormat::Double => Int::i64().mask(),
                FloatFormat::Single => Int::i32().mask(),
            },
        }
    }

    pub fn value(&self) -> u64 {
        self.constant & self.mask
    }
}

impl Instruction for FConstInst {
    fn operands(&self) -> &[Value] {
        &[]
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.ty)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct BConstInst {
    constant: bool,
    ty: Type,
}

impl BConstInst {
    fn new(ty: Type, constant: bool) -> Self {
        Self { constant, ty }
    }

    pub fn value(&self) -> bool {
        self.constant
    }
}

impl Instruction for BConstInst {
    fn operands(&self) -> &[Value] {
        &[]
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.ty)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct UndefConstInst {
    ty: Type,
}

impl UndefConstInst {
    fn new(ty: Type) -> Self {
        Self { ty }
    }
}

impl Instruction for UndefConstInst {
    fn operands(&self) -> &[Value] {
        &[]
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.ty)
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct NullConstInst {
    ty: Type,
}

impl NullConstInst {
    fn new(ty: Type) -> Self {
        Self { ty }
    }
}

impl Instruction for NullConstInst {
    fn operands(&self) -> &[Value] {
        &[]
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.ty)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct GlobalAddrInst {
    name: String,
}

impl GlobalAddrInst {
    fn new(name: String) -> Self {
        Self { name }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl Instruction for GlobalAddrInst {
    fn operands(&self) -> &[Value] {
        &[]
    }

    fn result_ty(&self) -> Option<Type> {
        Some(self.ty)
    }
}

impl Instruction for InstData {
    fn operands(&self) -> &[Value] {
        match &self.data {
            InstData::Call(e) => e.operands(),
            InstData::IndirectCall(e) => e.operands(),
            InstData::ICmp(e) => e.operands(),
            InstData::FCmp(e) => e.operands(),
            InstData::Sel(e) => e.operands(),
            InstData::Br(e) => e.operands(),
            InstData::CondBr(e) => e.operands(),
            InstData::Switch(e) => e.operands(),
            InstData::Unreachable(e) => e.operands(),
            InstData::Ret(e) => e.operands(),
            InstData::And(e) => e.operands(),
            InstData::Or(e) => e.operands(),
            InstData::Xor(e) => e.operands(),
            InstData::Shl(e) => e.operands(),
            InstData::AShr(e) => e.operands(),
            InstData::LShr(e) => e.operands(),
            InstData::IAdd(e) => e.operands(),
            InstData::ISub(e) => e.operands(),
            InstData::IMul(e) => e.operands(),
            InstData::SDiv(e) => e.operands(),
            InstData::UDiv(e) => e.operands(),
            InstData::SRem(e) => e.operands(),
            InstData::URem(e) => e.operands(),
            InstData::FNeg(e) => e.operands(),
            InstData::FAdd(e) => e.operands(),
            InstData::FSub(e) => e.operands(),
            InstData::FMul(e) => e.operands(),
            InstData::FDiv(e) => e.operands(),
            InstData::FRem(e) => e.operands(),
            InstData::Alloca(e) => e.operands(),
            InstData::Load(e) => e.operands(),
            InstData::Store(e) => e.operands(),
            InstData::Offset(e) => e.operands(),
            InstData::Extract(e) => e.operands(),
            InstData::Insert(e) => e.operands(),
            InstData::Elemptr(e) => e.operands(),
            InstData::Sext(e) => e.operands(),
            InstData::Zext(e) => e.operands(),
            InstData::Trunc(e) => e.operands(),
            InstData::IToB(e) => e.operands(),
            InstData::BToI(e) => e.operands(),
            InstData::SIToF(e) => e.operands(),
            InstData::UIToF(e) => e.operands(),
            InstData::FToSI(e) => e.operands(),
            InstData::FToUI(e) => e.operands(),
            InstData::IToP(e) => e.operands(),
            InstData::PToI(e) => e.operands(),
            InstData::IConst(e) => e.operands(),
            InstData::FConst(e) => e.operands(),
            InstData::BConst(e) => e.operands(),
            InstData::GlobalAddr(e) => e.operands(),
            InstData::BlockArg(e) => e.operands(),
        }
    }

    fn result_ty(&self) -> Option<Type> {
        match &self.opcode {
            InstData::Call(e) => e.result_ty(),
            InstData::IndirectCall(e) => e.result_ty(),
            InstData::ICmp(e) => e.result_ty(),
            InstData::FCmp(e) => e.result_ty(),
            InstData::Sel(e) => e.result_ty(),
            InstData::Br(e) => e.result_ty(),
            InstData::CondBr(e) => e.result_ty(),
            InstData::Switch(e) => e.result_ty(),
            InstData::Unreachable(e) => e.result_ty(),
            InstData::Ret(e) => e.result_ty(),
            InstData::And(e) => e.result_ty(),
            InstData::Or(e) => e.result_ty(),
            InstData::Xor(e) => e.result_ty(),
            InstData::Shl(e) => e.result_ty(),
            InstData::AShr(e) => e.result_ty(),
            InstData::LShr(e) => e.result_ty(),
            InstData::IAdd(e) => e.result_ty(),
            InstData::ISub(e) => e.result_ty(),
            InstData::IMul(e) => e.result_ty(),
            InstData::SDiv(e) => e.result_ty(),
            InstData::UDiv(e) => e.result_ty(),
            InstData::SRem(e) => e.result_ty(),
            InstData::URem(e) => e.result_ty(),
            InstData::FNeg(e) => e.result_ty(),
            InstData::FAdd(e) => e.result_ty(),
            InstData::FSub(e) => e.result_ty(),
            InstData::FMul(e) => e.result_ty(),
            InstData::FDiv(e) => e.result_ty(),
            InstData::FRem(e) => e.result_ty(),
            InstData::Alloca(e) => e.result_ty(),
            InstData::Load(e) => e.result_ty(),
            InstData::Store(e) => e.result_ty(),
            InstData::Offset(e) => e.result_ty(),
            InstData::Extract(e) => e.result_ty(),
            InstData::Insert(e) => e.result_ty(),
            InstData::Elemptr(e) => e.result_ty(),
            InstData::Sext(e) => e.result_ty(),
            InstData::Zext(e) => e.result_ty(),
            InstData::Trunc(e) => e.result_ty(),
            InstData::IToB(e) => e.result_ty(),
            InstData::BToI(e) => e.result_ty(),
            InstData::SIToF(e) => e.result_ty(),
            InstData::UIToF(e) => e.result_ty(),
            InstData::FToSI(e) => e.result_ty(),
            InstData::FToUI(e) => e.result_ty(),
            InstData::IToP(e) => e.result_ty(),
            InstData::PToI(e) => e.result_ty(),
            InstData::IConst(e) => e.result_ty(),
            InstData::FConst(e) => e.result_ty(),
            InstData::BConst(e) => e.result_ty(),
            InstData::GlobalAddr(e) => e.result_ty(),
        }
    }
}
