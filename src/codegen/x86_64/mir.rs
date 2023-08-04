//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::X86_64;
use crate::codegen::{
    CallUseDefId, MIRBlock, MachInst, PReg, Reg, RegCollector, RegToRegCopy, StackFrame,
    UnconditionalBranch, VariableLocation, WriteableReg,
};
use crate::utility::Str;
use static_assertions::assert_eq_size;

/// Extremely compact way of storing the width (in bytes) of the input and output
/// of an instruction.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct WidthPair {
    data: u8,
}

impl WidthPair {
    /// Creates a new [`WidthPair`] with two widths, both in bits. Each width must be `<= 64`, a power
    /// of two, and divisible by `8`.
    #[inline]
    pub fn from_bits(src_width: usize, dest_width: usize) -> Self {
        debug_assert!(src_width <= 64 && src_width.is_power_of_two() && src_width % 8 == 0);
        debug_assert!(dest_width <= 64 && dest_width.is_power_of_two() && dest_width % 8 == 0);

        Self {
            data: ((src_width / 8) as u8) << 4 | ((dest_width / 8) as u8),
        }
    }

    /// Creates a new [`WidthPair`] with two widths, both in bytes. Each width must be `<= 8` and a power
    /// of two.
    #[inline]
    pub fn from_bytes(src_width: usize, dest_width: usize) -> Self {
        debug_assert!(src_width <= 8 && src_width.is_power_of_two());
        debug_assert!(dest_width <= 8 && dest_width.is_power_of_two());

        Self {
            data: (src_width as u8) << 4 | (dest_width as u8),
        }
    }

    /// Creates a new [`WidthPair`] from two [`Width`] objects
    #[inline]
    pub fn from_widths(src_width: Width, dest_width: Width) -> Self {
        Self::from_bytes(src_width.into_bytes(), dest_width.into_bytes())
    }

    /// Gets the width of the source in bytes
    #[inline]
    pub fn src_bytes(self) -> usize {
        ((self.data & 0xF0) >> 4) as usize
    }

    /// Gets the width of the source in bits
    #[inline]
    pub fn src_bits(self) -> usize {
        (((self.data & 0xF0) >> 4) as usize) * 8
    }

    /// Gets the width of the destination in bytes
    #[inline]
    pub fn dest_bytes(self) -> usize {
        (self.data & 0x0F) as usize
    }

    /// Gets the width of the destination in bytes
    #[inline]
    pub fn dest_bits(self) -> usize {
        ((self.data & 0x0F) as usize) * 8
    }

    /// Gets the source size as an [`Width`]
    #[inline]
    pub fn src_width(self) -> Width {
        Width::from_bytes(self.src_bytes())
    }

    /// Gets the source size as an [`Width`]
    #[inline]
    pub fn dest_width(self) -> Width {
        Width::from_bytes(self.dest_bytes())
    }
}

/// The size of an operand. For [`Reg`]s, this is the specific size of that
/// register being used. For [`IndirectAddress`]s, this is the size of the value being
/// loaded.
#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum Width {
    /// A single byte
    Byte,
    /// A word, i.e. 2 bytes
    Word,
    /// A double word, i.e. 4 bytes
    Dword,
    /// A quad word, i.e. 8 bytes
    Qword,
}

impl Width {
    /// Creates an [`Width`] from a size in bytes
    #[inline]
    pub const fn from_bytes(bytes: usize) -> Self {
        match bytes {
            1 => Width::Byte,
            2 => Width::Word,
            4 => Width::Dword,
            8 => Width::Qword,
            _ => panic!("illegal size for `x64::OperandSize`"),
        }
    }

    /// Converts back into a raw byte count
    #[inline]
    pub const fn into_bytes(self) -> usize {
        match self {
            Width::Byte => 1,
            Width::Word => 2,
            Width::Dword => 4,
            Width::Qword => 8,
        }
    }
}

impl From<Width> for WidthPair {
    fn from(value: Width) -> Self {
        let bytes = value.into_bytes();

        Self::from_bytes(bytes, bytes)
    }
}

/// The possible scalar (multiply) values for indirect addressing.
#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum Scale {
    /// `x*1`
    One,
    /// `x*2`
    Two,
    /// `x*4`
    Four,
    /// `x*8`
    Eight,
}

impl From<Scale> for i32 {
    fn from(value: Scale) -> i32 {
        match value {
            Scale::One => 1,
            Scale::Two => 2,
            Scale::Four => 4,
            Scale::Eight => 8,
        }
    }
}

/// This type is a compact representation of a `(Scale, i32)` tuple, with a slight limitation
/// that the `i32` must actually be representable in 2's complement 30-bit (i.e. must be
/// within the range `[-2^29, 2^29 - 1]`).
///
/// This compactly stores a 30-bit signed offset **and** a scale of either 1, 2, 4 or 8.
/// While x86-64 can technically use offsets of up to 32-bit, that would force [`Inst`]s
/// to be larger than 32 bytes. I think this is a worthwhile trade-off. It's a compromise between
/// keeping my [`Inst`] representation relatively compact and representing a wide variety of instructions.
///
/// The offset is stored in two's complement
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct ScaleAnd30BitOffset {
    data: u32,
}

impl ScaleAnd30BitOffset {
    const NUM_BITS: u32 = 30;

    /// 2^(30 - 1) - 1`, the maximum value that can be stored as an offset
    pub const MAXIMUM_OFFSET: i32 = (2i32).pow(Self::NUM_BITS - 1) - 1;

    /// `-2^(30 - 1)`, the minimum value that can be stored as an offset
    pub const MINIMUM_OFFSET: i32 = -((2i32).pow(Self::NUM_BITS - 1));

    const SCALE_MASK: u32 = (0b11 << Self::NUM_BITS);

    const OFFSET_MASK: u32 = !Self::SCALE_MASK;

    /// Creates a compact representation. `offset` must be within the range
    /// `[MINIMUM_OFFSET, MAXIMUM_OFFSET]`.
    pub const fn new(scale: Scale, offset: i32) -> Self {
        let raw = Self::twos_complement_30bit(offset);
        let scale_2bit = Self::scale_2bit(scale);

        Self {
            data: raw | (scale_2bit << Self::NUM_BITS),
        }
    }

    /// Gets the scale back out of the representation
    pub const fn scale(self) -> Scale {
        match self.data & Self::SCALE_MASK {
            0b0000_0000_0000_0000_0000_0000_0000_0000 => Scale::One,
            0b0100_0000_0000_0000_0000_0000_0000_0000 => Scale::Two,
            0b1000_0000_0000_0000_0000_0000_0000_0000 => Scale::Four,
            0b1100_0000_0000_0000_0000_0000_0000_0000 => Scale::Eight,
            _ => unreachable!(),
        }
    }

    /// Gets the offset back out of the representation through a software-level sign extension
    pub const fn offset(self) -> i32 {
        let raw = self.data & Self::OFFSET_MASK;

        // if the value is negative, we need to 'sign extend' it
        if raw & (0b1 << (Self::NUM_BITS - 1)) != 0 {
            // scale_mask has the top 2 bits set, we OR that with the raw
            // to "sign extend" it to 32-bits
            (raw | Self::SCALE_MASK) as i32
        } else {
            raw as i32
        }
    }

    /// Gets the data held inside in an expanded form
    pub const fn expand(self) -> (Scale, i32) {
        (self.scale(), self.offset())
    }

    #[inline]
    const fn scale_2bit(scale: Scale) -> u32 {
        match scale {
            Scale::One => 0b00,
            Scale::Two => 0b01,
            Scale::Four => 0b10,
            Scale::Eight => 0b11,
        }
    }

    #[inline]
    const fn twos_complement_30bit(offset: i32) -> u32 {
        assert!(
            offset >= Self::MINIMUM_OFFSET && offset <= Self::MAXIMUM_OFFSET,
            "cannot represent offsets that require more than 30 bits directly"
        );

        // any negative offsets within range will have leading 1s, we can shave those off.
        // e.g. in 2s complement 32-bit, -536870912 (minimum offset) is represented by
        // 11100000000000000000000000000000. We can shave off top 2 bits and get an equivalent.
        //
        // any positive offsets can be bit-casted directly too, they just have 0s in the bits
        // that we want to shave off.
        (offset as u32) & Self::OFFSET_MASK
    }
}

/// An operand to an instruction that references a memory location and loads a value
/// of a specific size.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum IndirectAddress {
    /// Loading from a pointer stored in a register, i.e. `[reg]`
    Reg(Reg),
    /// Adding an offset in reg2 to a base in reg1 and loading, i.e. `[reg1 + reg2]`
    RegReg(Reg, Reg),
    /// Adding a constant offset to a register and loading, i.e. `[reg + offset]`
    RegOffset(Reg, i32),
    /// An offset from `rsp`. The storage is (offset, lo of stacksize, hi of stacksize)
    /// because due to the extreme layout manipulation that Rust is doing, storing this as
    /// a `usize` or `u64` actually makes `Inst` bigger than 32 bytes
    StackOffset(i32, u32, u32),
    /// Scales a register by a scalar and then uses that, i.e. `[reg*scale]`
    ScaledReg(Reg, Scale),
    /// Adds a register to another register that's scaled, i.e. `[reg1 + reg2*scale`]
    RegScaledReg(Reg, Reg, Scale),
    /// Adds a register to another register that's scaled, and adds a final offset. `[reg1 + reg2*scale + index`]
    RegScaledRegIndex(Reg, Reg, ScaleAnd30BitOffset),
    /// This is the `[rip + global]` addressing mode for accessing a global
    RipGlobal(Str),
}

impl IndirectAddress {
    /// Properly creates a [`Self::StackOffset`].
    #[inline]
    pub fn stack_offset(offset: i32, stack_size: usize) -> Self {
        Self::StackOffset(offset, stack_size as u32, (stack_size >> 32) as u32)
    }
}

assert_eq_size!(IndirectAddress, [u64; 2]);

/// The possible operands for instructions that can deal with more than just registers
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum RegMemImm {
    /// Using a register's value directly, i.e. `reg` in x86-64 assembly
    Reg(Reg),
    /// A memory location to be loaded from
    Mem(IndirectAddress),
    /// A signed immediate value, i.e. `$imm` in x86-64 assembly
    Imm(i32),
}

/// The possible operands for instructions that can deal with either
/// registers or in-line memory accesses
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum RegMem {
    /// Using a register's value directly, i.e. `reg` in x86-64 assembly
    Reg(Reg),
    /// A memory location to be loaded from
    Mem(IndirectAddress),
}

/// The possible operands for instructions that can deal with either
/// registers or in-line memory accesses
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum RegImm {
    /// Using a register's value directly, i.e. `reg` in x86-64 assembly
    Reg(Reg),
    /// A memory location to be loaded from
    Imm(i32),
}

impl From<RegMem> for RegMemImm {
    #[inline(always)]
    fn from(value: RegMem) -> Self {
        match value {
            RegMem::Reg(reg) => RegMemImm::Reg(reg),
            RegMem::Mem(mem) => RegMemImm::Mem(mem),
        }
    }
}

impl From<RegImm> for RegMemImm {
    #[inline(always)]
    fn from(value: RegImm) -> Self {
        match value {
            RegImm::Reg(reg) => RegMemImm::Reg(reg),
            RegImm::Imm(imm) => RegMemImm::Imm(imm),
        }
    }
}

/// A `nop` instruction with a specified byte length
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Nop {
    /// The desired length in bytes of the `nop`
    pub bytes: u8,
}

/// A `lea` that computes an address, and then puts it into `dest`
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Lea {
    /// The value being stored into memory
    pub src: IndirectAddress,
    /// The destination register to copy to
    pub dest: WriteableReg,
}

/// A `mov` into a register
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Mov {
    /// The size of the operand and the destination
    pub width: Width,
    /// The value being stored into memory
    pub src: RegMemImm,
    /// The destination register to copy to
    pub dest: WriteableReg,
}

/// A `mov` that stores into memory
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct MovStore {
    /// The size of the operand and the destination
    pub width: Width,
    /// The value being stored into memory
    pub src: RegImm,
    /// The destination location in memory
    pub dest: IndirectAddress,
}

/// Zero-extending copy instruction between two locations
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Movzx {
    /// A pair of widths for the source and destinations
    pub widths: WidthPair,
    /// The source of the zero-extend
    pub src: RegMemImm,
    /// The destination of the zero-extend
    pub dest: WriteableReg,
}

/// Sign-extending copy instruction between two locations
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Movsx {
    /// A pair of widths for the source and destinations
    pub widths: WidthPair,
    /// The source of the sign-extend
    pub src: RegMemImm,
    /// The destination of the sign-extend
    pub dest: WriteableReg,
}

/// Copies a 64-bit value into a register
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Movabs {
    /// The value to move into a register
    pub value: u64,
    /// The destination of the sign-extend
    pub dest: WriteableReg,
}

/// The opcode of A specific ALU instruction
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum ALUOpcode {
    /// Bitwise `and` instruction
    And,
    /// Bitwise `or` instruction
    Or,
    /// Bitwise `xor` instruction
    Xor,
    /// Logical left shift instruction
    Shl,
    /// Arithmetic right shift instruction
    Sar,
    /// Logical right shift instruction
    Shr,
    /// Two's complement `add` instruction
    Add,
    /// Two's complement `sub` instruction
    Sub,
}

/// An ALU instruction with a given opcode that operates on two registers.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct ALU {
    /// The operation being performed
    pub opc: ALUOpcode,
    /// A width for the operands
    pub width: Width,
    /// Register where the first operand is located. This is also the destination.
    pub lhs: WriteableReg,
    /// Second operand
    pub rhs: RegMemImm,
}

/// Performs bitwise NOT on a register
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Not {
    /// The size of the value being NOT-ed
    pub width: Width,
    /// The register to NOT
    pub reg: WriteableReg,
}

/// Negates the (signed) value in a register
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Neg {
    /// The size of the value being NEG-ed
    pub width: Width,
    /// The register to negate
    pub reg: WriteableReg,
}

/// Multiplies two integers and gets a 128bit result
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct IMul {
    /// The size of the values being multiplied
    pub width: Width,
    /// The left-hand side, also the destination of the low bits
    pub lhs: WriteableReg,
    /// The right-hand operand
    pub rhs: RegMemImm,
}

/// Copies the sign bit of the 16-bit source (always `ax`) into the dest (always `dx`)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cwd;

impl Cwd {
    /// The register being "sign-extended" into `DEST`
    pub const SRC: Reg = Reg::from_preg(X86_64::RAX);

    /// The register where the upper sign-extension bits go
    pub const DEST: Reg = Reg::from_preg(X86_64::RDX);
}

/// Copies the sign bit of the 32-bit source (always `eax`) into the dest (always `edx`)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cdq;

impl Cdq {
    /// The register being "sign-extended" into `DEST`
    pub const SRC: Reg = Reg::from_preg(X86_64::RAX);

    /// The register where the upper sign-extension bits go
    pub const DEST: Reg = Reg::from_preg(X86_64::RDX);
}

/// Copies the sign bit of the 64-bit source (always `rax`) into the dest (always `rdx`)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cqo;

impl Cqo {
    /// The register being "sign-extended" into `DEST`
    pub const SRC: Reg = Reg::from_preg(X86_64::RAX);

    /// The register where the upper sign-extension bits go
    pub const DEST: Reg = Reg::from_preg(X86_64::RDX);
}

/// Performs signed integer division. The following assumptions are made:
///
/// 1. The dividend is stored in RDX:RAX (adjusted for width)
/// 2. The quotient will be stored into RAX (adjusted for width)
/// 3. The remainder will be stored into RDX (adjusted for width)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct IDiv {
    /// The value being divided by.
    pub divisor: RegMem,
    /// The width of the division
    pub width: Width,
}

impl IDiv {
    /// The register where the low bits of the dividend must be located
    pub const DIVIDEND_LO: Reg = Reg::from_preg(X86_64::RAX);

    /// The register where the high bits of the dividend must be located
    pub const DIVIDEND_HI: Reg = Reg::from_preg(X86_64::RDX);

    /// The register where the quotient will be put
    pub const QUOTIENT: Reg = Self::DIVIDEND_LO;

    /// The register where the remainder will be put
    pub const REMAINDER: Reg = Self::DIVIDEND_HI;
}

/// Performs unsigned integer division. The following assumptions are made:
///
/// 1. The dividend is stored in RDX:RAX (adjusted for width)
/// 2. The quotient will be stored into RAX (adjusted for width)
/// 3. The remainder will be stored into RDX (adjusted for width)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Div {
    /// The value being divided by.
    pub divisor: RegMem,
    /// The width of the division
    pub width: Width,
}

impl Div {
    /// The register where the low bits of the dividend must be located
    pub const DIVIDEND_LO: Reg = Reg::from_preg(X86_64::RAX);

    /// The register where the high bits of the dividend must be located
    pub const DIVIDEND_HI: Reg = Reg::from_preg(X86_64::RDX);

    /// The register where the quotient will be put
    pub const QUOTIENT: Reg = Self::DIVIDEND_LO;

    /// The register where the remainder will be put
    pub const REMAINDER: Reg = Self::DIVIDEND_HI;
}

/// A `cmp` instruction. Subtracts two values, discards the result, and updates CPU flags.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cmp {
    /// A width for the two operands
    pub width: Width,
    /// First operand
    pub lhs: Reg,
    /// Second operand
    pub rhs: RegMemImm,
}

/// A `test` instruction. Performs bitwise AND between two values, discards the result, and
/// updates CPU flags.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Test {
    /// A width for the two operands
    pub width: Width,
    /// First operand
    pub lhs: Reg,
    /// Second operand
    pub rhs: RegMemImm,
}

/// A condition code, used by several instructions to do operations
/// based on the state of the CPU's status flags
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum ConditionCode {
    /// Jump if equal
    E,
    /// Jump if not equal
    NE,
    /// Jump if zero (equivalent to JE, but we want different assembly)
    Z,
    /// Jump if not zero (equivalent to JNE, but we want different assembly)
    NZ,
    /// Jump if greater than (signed)
    G,
    /// Jump if greater than or equal to (signed)
    GE,
    /// Jump if less than (signed)
    L,
    /// Jump if less than or equal to (signed)
    LE,
    /// Jump if greater than (unsigned)
    A,
    /// Jump if greater than or equal to (unsigned)
    AE,
    /// Jump if less than (unsigned)
    B,
    /// Jump if less than or equal to (unsigned)
    BE,
    /// Jump if negative
    S,
    /// Jump if positive
    NS,
    /// Jump if overflowed
    O,
    /// Jump if not overflowed
    NO,
}

/// A `setCC` instruction, used to set a byte based on a condition
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Set {
    /// The condition to set the byte based on
    pub condition: ConditionCode,
    /// The register to write to (assumed to be the bottom byte of it)
    pub dest: WriteableReg,
}

/// A target that a `jmp` instruction could target
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum JumpTarget {
    /// A global entity, e.g. a function
    Global(Str),
    /// A local entity, usually a block label
    Local(MIRBlock),
}

/// Possibly jumps to a block or target
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Jump {
    /// The condition of the jump. If this is `None` this is unconditional
    pub condition: Option<ConditionCode>,
    /// The target of the jump
    pub target: JumpTarget,
}

/// Pushes the value of a register onto the stack
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Push {
    /// The register to push
    pub value: Reg,
    /// The width of the push
    pub width: Width,
}

/// Pops a value from the stack and writes it to `dest`
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Pop {
    /// The destination for the top value of the stack
    pub dest: WriteableReg,
    /// The width of the pop
    pub width: Width,
}

/// Calls a known function
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Call {
    /// The name of the function to call
    pub func: Str,
    /// An ID that can be used to access use-def info from the stack frame
    pub id: CallUseDefId,
}

/// Performs an indirect call to a register, function pointer in memory, etc.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct IndirectCall {
    /// Where the function pointer is located
    pub func: RegMemImm,
    /// An ID that can be used to access use-def info from the stack frame
    pub id: CallUseDefId,
}

/// Returns from the current function
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Ret {}

/// An undefined instruction that generates a trap when executed
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Ud2 {}

/// Models a single machine instruction for the x86_64 backend.
#[repr(u32)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub enum Inst {
    /// A no-op instruction
    Nop(Nop),
    /// A `mov` into a register
    Mov(Mov),
    /// A `movzx` that performs zero-extension
    Movzx(Movzx),
    /// A `movsx` that performs sign-extension
    Movsx(Movsx),
    /// A `mov` that stores into memory
    MovStore(MovStore),
    /// Moves a 64-bit constant into a register
    Movabs(Movabs),
    /// An `lea` instruction that computes an address
    Lea(Lea),
    /// An ALU instruction with a given opcode that operates on two registers.
    ALU(ALU),
    /// Performs bitwise NOT on a register
    Not(Not),
    /// Negates the (signed) value in a register
    Neg(Neg),
    /// A multiplication that produces a 128-bit result
    IMul(IMul),
    /// Broadcasts the sign bit of `ax` into `dx`
    Cwd(Cwd),
    /// Broadcasts the sign bit of `eax` into `edx`
    Cdq(Cdq),
    /// Broadcasts the sign bit of `rax` into `rdx`
    Cqo(Cqo),
    /// Performs unsigned division
    Div(Div),
    /// Performs signed division
    IDiv(IDiv),
    /// A comparison between two integers
    Cmp(Cmp),
    /// A different comparison between two integers
    Test(Test),
    /// Sets a byte based on a condition
    Set(Set),
    /// Pushes the value of a register onto the stack
    Push(Push),
    /// Pops a value from the stack and writes it to `dest`
    Pop(Pop),
    /// A jump to a local location in the function
    Jump(Jump),
    /// Calls a known function
    Call(Call),
    /// Performs an indirect call
    IndirectCall(IndirectCall),
    /// Returns from the function
    Ret(Ret),
    /// An undefined instruction that generates a trap when executed
    Ud2(Ud2),
}

assert_eq_size!(Inst, [u64; 4]);

macro_rules! push_if_reg {
    (RegMemImm, $e:expr, $width:expr, $collector:expr) => {
        match $e {
            RegMemImm::Reg(r) => $collector.push((r, $width.into_bytes() as u32)),
            RegMemImm::Mem(loc) => {
                push_if_reg!(IndirectAddress, loc, $collector);
            }
            RegMemImm::Imm(_) => {}
        }
    };

    (IndirectAddress, $e:expr, $collector:expr) => {
        match $e {
            IndirectAddress::Reg(r) | IndirectAddress::RegOffset(r, _) => $collector.push((r, 8)),
            IndirectAddress::StackOffset(_, _, _) => {
                $collector.push((Reg::from_preg(X86_64::RSP), 8))
            }
            IndirectAddress::RegReg(r1, r2) => {
                $collector.push((r1, 8));
                $collector.push((r2, 8));
            }
            IndirectAddress::ScaledReg(reg, _) => {
                $collector.push((reg, 8));
            }
            IndirectAddress::RegScaledReg(r1, r2, _) => {
                $collector.push((r1, 8));
                $collector.push((r2, 8));
            }
            IndirectAddress::RegScaledRegIndex(r1, r2, _) => {
                $collector.push((r1, 8));
                $collector.push((r2, 8));
            }
            IndirectAddress::RipGlobal(_) => {}
        }
    };

    (RegMem, $e:expr, $width:expr, $collector:expr) => {
        match $e {
            RegMem::Reg(r) => $collector.push((r, $width.into_bytes() as u32)),
            RegMem::Mem(loc) => {
                push_if_reg!(IndirectAddress, loc, $collector);
            }
        }
    };

    (RegImm, $e:expr, $width:expr, $collector:expr) => {
        match $e {
            RegImm::Reg(r) => $collector.push((r, $width.into_bytes() as u32)),
            RegImm::Imm(_) => {}
        }
    };
}

macro_rules! rewrite_for {
    ($reg:expr, $rewrites:expr, $frame:expr) => {{
        let mut result = $reg;

        for &(reg, preg) in $rewrites {
            if reg == $reg {
                result = Reg::from_preg(preg);
            }
        }

        result
    }};

    (rmi, $rmi:expr, $rewrites:expr, $frame:expr) => {{
        match $rmi {
            RegMemImm::Reg(r) => RegMemImm::Reg(rewrite_for!(r, $rewrites, $frame)),
            RegMemImm::Mem(m) => RegMemImm::Mem(rewrite_for!(mem, m, $rewrites, $frame)),
            RegMemImm::Imm(i) => RegMemImm::Imm(i),
        }
    }};

    (rm, $rm:expr, $rewrites:expr, $frame:expr) => {{
        match $rm {
            RegMem::Reg(r) => RegMem::Reg(rewrite_for!(r, $rewrites, $frame)),
            RegMem::Mem(m) => RegMem::Mem(rewrite_for!(mem, m, $rewrites, $frame)),
        }
    }};

    (ri, $ri:expr, $rewrites:expr, $frame:expr) => {{
        match $ri {
            RegImm::Reg(r) => RegImm::Reg(rewrite_for!(r, $rewrites, $frame)),
            RegImm::Imm(i) => RegImm::Imm(i),
        }
    }};

    (mem, $mem:expr, $rewrites:expr, $frame:expr) => {{
        match $mem {
            IndirectAddress::Reg(r) => IndirectAddress::Reg(rewrite_for!(r, $rewrites, $frame)),
            IndirectAddress::StackOffset(offset, lo, hi) => {
                let old_size = ((hi as usize) << 8) | lo as usize;

                if $frame.stack_size() != old_size {
                    // only gets bigger
                    let diff = $frame.stack_size() - old_size;

                    IndirectAddress::RegOffset(Reg::from_preg(X86_64::RSP), offset + (diff as i32))
                } else {
                    IndirectAddress::RegOffset(Reg::from_preg(X86_64::RSP), offset)
                }
            }
            IndirectAddress::RegReg(r1, r2) => IndirectAddress::RegReg(
                rewrite_for!(r1, $rewrites, $frame),
                rewrite_for!(r2, $rewrites, $frame),
            ),
            IndirectAddress::RegOffset(r, imm) => {
                IndirectAddress::RegOffset(rewrite_for!(r, $rewrites, $frame), imm)
            }
            IndirectAddress::ScaledReg(r, scale) => {
                IndirectAddress::ScaledReg(rewrite_for!(r, $rewrites, $frame), scale)
            }
            IndirectAddress::RegScaledReg(r1, r2, scale) => IndirectAddress::RegScaledReg(
                rewrite_for!(r1, $rewrites, $frame),
                rewrite_for!(r2, $rewrites, $frame),
                scale,
            ),
            IndirectAddress::RegScaledRegIndex(r1, r2, scale_index) => {
                IndirectAddress::RegScaledRegIndex(
                    rewrite_for!(r1, $rewrites, $frame),
                    rewrite_for!(r2, $rewrites, $frame),
                    scale_index,
                )
            }
            IndirectAddress::RipGlobal(s) => IndirectAddress::RipGlobal(s),
        }
    }};
}

#[inline(always)]
fn into_pair(reg: Reg, width: Width) -> (Reg, u32) {
    (reg, width.into_bytes() as u32)
}

impl MachInst for Inst {
    type Arch = X86_64;

    fn uses<const N: usize>(
        &self,
        frame: &dyn StackFrame<X86_64>,
        collector: &mut RegCollector<N>,
    ) {
        match self {
            Inst::Nop(_) => {}
            Inst::Mov(mov) => {
                push_if_reg!(RegMemImm, mov.src, mov.width, collector);
            }
            Inst::Movzx(movzx) => {
                push_if_reg!(RegMemImm, movzx.src, movzx.widths.src_width(), collector);
            }
            Inst::Movsx(movsx) => {
                push_if_reg!(RegMemImm, movsx.src, movsx.widths.src_width(), collector);
            }
            Inst::MovStore(mov) => {
                push_if_reg!(RegImm, mov.src, mov.width, collector);
                push_if_reg!(IndirectAddress, mov.dest, collector);
            }
            Inst::Lea(lea) => {
                push_if_reg!(IndirectAddress, lea.src, collector);
            }
            Inst::ALU(alu) => {
                push_if_reg!(RegMemImm, alu.rhs, alu.width, collector);
                collector.push(into_pair(alu.lhs.to_reg(), alu.width));
            }
            Inst::Not(not) => {
                collector.push(into_pair(not.reg.to_reg(), not.width));
            }
            Inst::Neg(neg) => {
                collector.push(into_pair(neg.reg.to_reg(), neg.width));
            }
            Inst::IMul(mul) => {
                push_if_reg!(RegMemImm, mul.rhs, mul.width, collector);
                collector.push(into_pair(mul.lhs.to_reg(), mul.width));
            }
            Inst::Cmp(cmp) => {
                push_if_reg!(RegMemImm, cmp.rhs, cmp.width, collector);
                collector.push(into_pair(cmp.lhs, cmp.width));
            }
            Inst::Test(test) => {
                push_if_reg!(RegMemImm, test.rhs, test.width, collector);
                collector.push(into_pair(test.lhs, test.width));
            }
            Inst::Set(_) => {}
            Inst::Push(push) => {
                collector.push(into_pair(push.value, push.width));
            }
            Inst::Pop(_) => {}
            Inst::Movabs(_) => {}
            Inst::Cwd(cwd) => {
                collector.push(into_pair(Cwd::SRC, Width::Word));
            }
            Inst::Cdq(cdq) => {
                collector.push(into_pair(Cdq::SRC, Width::Dword));
            }
            Inst::Cqo(cqo) => {
                collector.push(into_pair(Cqo::SRC, Width::Qword));
            }
            Inst::Div(div) => {
                push_if_reg!(RegMem, div.divisor, div.width, collector);
                collector.push(into_pair(Div::DIVIDEND_LO, div.width));
                collector.push(into_pair(Div::DIVIDEND_HI, div.width));
            }
            Inst::IDiv(idiv) => {
                push_if_reg!(RegMem, idiv.divisor, idiv.width, collector);
                collector.push(into_pair(IDiv::DIVIDEND_LO, idiv.width));
                collector.push(into_pair(IDiv::DIVIDEND_HI, idiv.width));
            }
            Inst::Call(call) => {
                for &reg in frame.call_use_defs(call.id).0 {
                    // we can't assume width, and they're extended to 8 anyway
                    collector.push(into_pair(Reg::from_preg(reg), Width::Qword));
                }
            }
            Inst::IndirectCall(call) => {
                push_if_reg!(RegMemImm, call.func, Width::Qword, collector);

                for &reg in frame.call_use_defs(call.id).0 {
                    // we can't assume width, and they're extended to 8 anyway
                    collector.push(into_pair(Reg::from_preg(reg), Width::Qword));
                }
            }
            Inst::Jump(_) => {}
            Inst::Ret(_) => {
                for &reg in frame.ret_uses() {
                    collector.push(into_pair(Reg::from_preg(reg), Width::Qword));
                }
            }
            Inst::Ud2(_) => {}
        }
    }

    fn defs<const N: usize>(
        &self,
        frame: &dyn StackFrame<X86_64>,
        collector: &mut RegCollector<N>,
    ) {
        match self {
            Inst::Nop(_) => {}
            Inst::Mov(mov) => {
                collector.push(into_pair(mov.dest.to_reg(), mov.width));
            }
            Inst::Movzx(movzx) => {
                collector.push(into_pair(movzx.dest.to_reg(), movzx.widths.dest_width()));
            }
            Inst::Movsx(movsx) => {
                collector.push(into_pair(movsx.dest.to_reg(), movsx.widths.dest_width()));
            }
            Inst::MovStore(_) => {}
            Inst::Lea(lea) => {
                collector.push(into_pair(lea.dest.to_reg(), Width::Qword));
            }
            Inst::ALU(alu) => {
                collector.push(into_pair(alu.lhs.to_reg(), alu.width));
            }
            Inst::Not(not) => {
                collector.push(into_pair(not.reg.to_reg(), not.width));
            }
            Inst::Neg(neg) => {
                collector.push(into_pair(neg.reg.to_reg(), neg.width));
            }
            Inst::IMul(mul) => {
                collector.push(into_pair(mul.lhs.to_reg(), mul.width));
            }
            Inst::Cmp(_) => {}
            Inst::Test(_) => {}
            Inst::Set(set) => {
                collector.push(into_pair(set.dest.to_reg(), Width::Byte));
            }
            Inst::Push(_) => {}
            Inst::Pop(pop) => {
                collector.push(into_pair(pop.dest.to_reg(), pop.width));
            }
            Inst::Movabs(movabs) => {
                collector.push(into_pair(movabs.dest.to_reg(), Width::Qword));
            }
            Inst::Cwd(cwd) => {
                collector.push(into_pair(Cwd::DEST, Width::Word));
            }
            Inst::Cdq(cdq) => {
                collector.push(into_pair(Cdq::DEST, Width::Dword));
            }
            Inst::Cqo(cqo) => {
                collector.push(into_pair(Cqo::DEST, Width::Qword));
            }
            Inst::Div(div) => {
                collector.push(into_pair(Div::QUOTIENT, div.width));
                collector.push(into_pair(Div::REMAINDER, div.width));
            }
            Inst::IDiv(idiv) => {
                collector.push(into_pair(IDiv::QUOTIENT, idiv.width));
                collector.push(into_pair(IDiv::REMAINDER, idiv.width));
            }
            Inst::Call(call) => {
                for &reg in frame.call_use_defs(call.id).1 {
                    collector.push(into_pair(Reg::from_preg(reg), Width::Qword));
                }
            }
            Inst::IndirectCall(call) => {
                for &reg in frame.call_use_defs(call.id).1 {
                    collector.push(into_pair(Reg::from_preg(reg), Width::Qword));
                }
            }
            Inst::Jump(_) => {}
            Inst::Ret(_) => {}
            Inst::Ud2(_) => {}
        }
    }

    fn is_copy(&self) -> bool {
        match self {
            Self::Mov(mov) => matches!(mov.src, RegMemImm::Reg(_)),
            _ => false,
        }
    }

    fn as_copy(&self) -> Option<RegToRegCopy> {
        match self {
            Self::Mov(mov) => match mov.src {
                RegMemImm::Reg(src) => Some(RegToRegCopy {
                    width: mov.width.into_bytes(),
                    to: mov.dest,
                    from: src,
                }),
                _ => None,
            },
            _ => None,
        }
    }

    fn as_unconditional_jmp(&self) -> Option<UnconditionalBranch> {
        match self {
            Self::Jump(jmp) => match jmp.target {
                JumpTarget::Local(block) => jmp
                    .condition
                    .is_none()
                    .then_some(UnconditionalBranch { to: block }),
                _ => None,
            },
            _ => None,
        }
    }

    fn copy(width: usize, src: Reg, dest: WriteableReg) -> Self {
        Self::Mov(Mov {
            width: Width::from_bytes(width),
            src: RegMemImm::Reg(src),
            dest,
        })
    }

    fn load(width: usize, from: VariableLocation, to: PReg) -> Self {
        Self::Mov(Mov {
            width: Width::from_bytes(width),
            dest: WriteableReg::from_reg(Reg::from_preg(to)),
            src: match from {
                VariableLocation::InReg(r) => RegMemImm::Reg(r),
                VariableLocation::RelativeToSP(offset, size) => {
                    RegMemImm::Mem(IndirectAddress::stack_offset(offset, size))
                }
                VariableLocation::RelativeToFP(offset) => RegMemImm::Mem(
                    IndirectAddress::RegOffset(Reg::from_preg(X86_64::RBP), offset),
                ),
            },
        })
    }

    fn store(width: usize, from: PReg, to: VariableLocation) -> Self {
        Self::MovStore(MovStore {
            width: Width::from_bytes(width),
            src: RegImm::Reg(Reg::from_preg(from)),
            dest: match to {
                VariableLocation::InReg(r) => unreachable!(),
                VariableLocation::RelativeToSP(offset, stack_size) => {
                    IndirectAddress::stack_offset(offset, stack_size)
                }
                VariableLocation::RelativeToFP(offset) => {
                    IndirectAddress::RegOffset(Reg::from_preg(X86_64::RBP), offset)
                }
            },
        })
    }

    fn is_ret(&self) -> bool {
        matches!(self, Self::Ret(_))
    }

    fn rewrite(self, rewrites: &[(Reg, PReg)], frame: &dyn StackFrame<X86_64>) -> Self {
        match self {
            Inst::Nop(_) => self,
            Inst::Mov(mov) => {
                let src = rewrite_for!(rmi, mov.src, rewrites, frame);
                let dest = WriteableReg::from_reg(rewrite_for!(mov.dest.to_reg(), rewrites, frame));

                Inst::Mov(Mov {
                    src,
                    dest,
                    width: mov.width,
                })
            }
            Inst::Movzx(movzx) => {
                let src = rewrite_for!(rmi, movzx.src, rewrites, frame);
                let dest =
                    WriteableReg::from_reg(rewrite_for!(movzx.dest.to_reg(), rewrites, frame));

                Inst::Movzx(Movzx {
                    src,
                    dest,
                    widths: movzx.widths,
                })
            }
            Inst::Movsx(movsx) => {
                let src = rewrite_for!(rmi, movsx.src, rewrites, frame);
                let dest =
                    WriteableReg::from_reg(rewrite_for!(movsx.dest.to_reg(), rewrites, frame));

                Inst::Movsx(Movsx {
                    src,
                    dest,
                    widths: movsx.widths,
                })
            }
            Inst::MovStore(mov) => {
                let src = rewrite_for!(ri, mov.src, rewrites, frame);
                let dest = rewrite_for!(mem, mov.dest, rewrites, frame);

                Inst::MovStore(MovStore {
                    src,
                    dest,
                    width: mov.width,
                })
            }
            Inst::Movabs(movabs) => {
                let dest = rewrite_for!(movabs.dest.to_reg(), rewrites, frame);

                Inst::Movabs(Movabs {
                    value: movabs.value,
                    dest: WriteableReg::from_reg(dest),
                })
            }
            Inst::Lea(lea) => {
                let src = rewrite_for!(mem, lea.src, rewrites, frame);
                let dest = rewrite_for!(lea.dest.to_reg(), rewrites, frame);

                Inst::Lea(Lea {
                    src,
                    dest: WriteableReg::from_reg(dest),
                })
            }
            Inst::ALU(alu) => {
                let lhs = rewrite_for!(alu.lhs.to_reg(), rewrites, frame);
                let rhs = rewrite_for!(rmi, alu.rhs, rewrites, frame);

                Inst::ALU(ALU {
                    opc: alu.opc,
                    width: alu.width,
                    lhs: WriteableReg::from_reg(lhs),
                    rhs,
                })
            }
            Inst::Not(not) => {
                let reg = rewrite_for!(not.reg.to_reg(), rewrites, frame);

                Inst::Not(Not {
                    width: not.width,
                    reg: WriteableReg::from_reg(reg),
                })
            }
            Inst::Neg(neg) => {
                let reg = rewrite_for!(neg.reg.to_reg(), rewrites, frame);

                Inst::Neg(Neg {
                    width: neg.width,
                    reg: WriteableReg::from_reg(reg),
                })
            }
            Inst::IMul(imul) => {
                let lhs = rewrite_for!(imul.lhs.to_reg(), rewrites, frame);
                let rhs = rewrite_for!(rmi, imul.rhs, rewrites, frame);

                Inst::IMul(IMul {
                    width: imul.width,
                    lhs: WriteableReg::from_reg(lhs),
                    rhs,
                })
            }
            Inst::Cwd(_) => self,
            Inst::Cdq(_) => self,
            Inst::Cqo(_) => self,
            Inst::Div(div) => {
                let divisor = rewrite_for!(rm, div.divisor, rewrites, frame);

                Inst::Div(Div {
                    width: div.width,
                    divisor,
                })
            }
            Inst::IDiv(idiv) => {
                let divisor = rewrite_for!(rm, idiv.divisor, rewrites, frame);

                Inst::IDiv(IDiv {
                    width: idiv.width,
                    divisor,
                })
            }
            Inst::Cmp(cmp) => {
                let lhs = rewrite_for!(cmp.lhs, rewrites, frame);
                let rhs = rewrite_for!(rmi, cmp.rhs, rewrites, frame);

                Inst::Cmp(Cmp {
                    width: cmp.width,
                    lhs,
                    rhs,
                })
            }
            Inst::Test(test) => {
                let lhs = rewrite_for!(test.lhs, rewrites, frame);
                let rhs = rewrite_for!(rmi, test.rhs, rewrites, frame);

                Inst::Test(Test {
                    width: test.width,
                    lhs,
                    rhs,
                })
            }
            Inst::Set(set) => {
                let dest = rewrite_for!(set.dest.to_reg(), rewrites, frame);

                Inst::Set(Set {
                    condition: set.condition,
                    dest: WriteableReg::from_reg(dest),
                })
            }
            Inst::Push(push) => {
                let reg = rewrite_for!(push.value, rewrites, frame);

                Inst::Push(Push {
                    width: push.width,
                    value: reg,
                })
            }
            Inst::Pop(pop) => {
                let reg = rewrite_for!(pop.dest.to_reg(), rewrites, frame);

                Inst::Pop(Pop {
                    width: pop.width,
                    dest: WriteableReg::from_reg(reg),
                })
            }
            Inst::Jump(_) => self,
            Inst::Call(_) => self,
            Inst::IndirectCall(indirectcall) => {
                let func = rewrite_for!(rmi, indirectcall.func, rewrites, frame);

                Inst::IndirectCall(IndirectCall {
                    func,
                    id: indirectcall.id,
                })
            }
            Inst::Ret(_) => self,
            Inst::Ud2(_) => self,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scale_30bit_offset() {
        let scales = [Scale::One, Scale::Two, Scale::Four, Scale::Eight];
        let offsets = [
            0,
            1,
            48,
            ScaleAnd30BitOffset::MAXIMUM_OFFSET,
            ScaleAnd30BitOffset::MINIMUM_OFFSET,
            -3829,
            32,
            -1,
            38408238,
            255,
        ];

        for scale in scales {
            for offset in offsets {
                let compact = ScaleAnd30BitOffset::new(scale, offset);

                assert_eq!(compact.scale(), scale);
                assert_eq!(compact.offset(), offset);
            }
        }
    }

    #[test]
    #[should_panic]
    fn scale_30bit_offset_too_small() {
        let offset = ScaleAnd30BitOffset::MINIMUM_OFFSET - 1;
        let _ = ScaleAnd30BitOffset::new(Scale::One, offset);
    }

    #[test]
    #[should_panic]
    fn scale_30bit_offset_too_big() {
        let offset = ScaleAnd30BitOffset::MAXIMUM_OFFSET + 1;
        let _ = ScaleAnd30BitOffset::new(Scale::One, offset);
    }
}
