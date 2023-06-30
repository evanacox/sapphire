//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::X86_64;
use crate::codegen::{MIRBlock, MachInst, Move, Reg, RegCollector, WriteableReg};
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

    /// Gets the width of the source in bytes
    #[inline]
    pub fn src_bytes(self) -> usize {
        (self.data & 0xF0) as usize
    }

    /// Gets the width of the source in bits
    #[inline]
    pub fn src_bits(self) -> usize {
        ((self.data & 0xF0) as usize) * 8
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
    pub fn src_operand_size(self) -> Width {
        Width::from_bytes(self.src_bytes())
    }

    /// Gets the source size as an [`Width`]
    #[inline]
    pub fn dest_operand_size(self) -> Width {
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
    /// Scales a register by a scalar and then uses that, i.e. `[reg*scale]`
    ScaledReg(Reg, Scale),
    /// Adds a register to another register that's scaled, i.e. `[reg1 + reg2*scale`]
    RegScaledReg(Reg, Reg, Scale),
    /// Adds a register to another register that's scaled, and adds a final offset. `[reg1 + reg2*scale + index`]
    RegScaledRegIndex(Reg, Reg, ScaleAnd30BitOffset),
    /// This is the `[rip + global]` addressing mode for accessing a global
    RipGlobal(Str),
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
    /// The destination of the high bits of the multiplication
    pub dest_hi: WriteableReg,
}

/// Copies the sign bit of the 16-bit source (always `ax`) into the dest (always `dx`)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cwd {
    /// The register being "sign-extended"
    pub src: Reg,
    /// The register being filled with the sign bit
    pub dest: WriteableReg,
}

/// Copies the sign bit of the 32-bit source (always `eax`) into the dest (always `edx`)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cdq {
    /// The register being "sign-extended"
    pub src: Reg,
    /// The register being filled with the sign bit
    pub dest: WriteableReg,
}

/// Copies the sign bit of the 64-bit source (always `rax`) into the dest (always `rdx`)
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Cqo {
    /// The register being "sign-extended"
    pub src: Reg,
    /// The register being filled with the sign bit
    pub dest: WriteableReg,
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
}

/// Pops a value from the stack and writes it to `dest`
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Pop {
    /// The destination for the top value of the stack
    pub dest: WriteableReg,
}

/// Calls a known function
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Call {
    /// The name of the function to call
    pub func: Str,
}

/// Performs an indirect call to a register, function pointer in memory, etc.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct IndirectCall {
    /// Where the function pointer is located
    pub func: RegMemImm,
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
    /// A `mov` that stores into memory
    MovStore(MovStore),
    /// Moves a 64-bit constant into a register
    Movabs(Movabs),
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
    (RegMemImm, $e:expr, $collector:expr) => {
        match $e {
            RegMemImm::Reg(r) => $collector.push(r),
            RegMemImm::Mem(loc) => {
                push_if_reg!(IndirectAddress, loc, $collector);
            }
            RegMemImm::Imm(_) => {}
        }
    };

    (IndirectAddress, $e:expr, $collector:expr) => {
        match $e {
            IndirectAddress::Reg(r) | IndirectAddress::RegOffset(r, _) => $collector.push(r),
            IndirectAddress::RegReg(r1, r2) => {
                $collector.push(r1);
                $collector.push(r2);
            }
            IndirectAddress::ScaledReg(reg, _) => {
                $collector.push(reg);
            }
            IndirectAddress::RegScaledReg(r1, r2, _) => {
                $collector.push(r1);
                $collector.push(r2);
            }
            IndirectAddress::RegScaledRegIndex(r1, r2, _) => {
                $collector.push(r1);
                $collector.push(r2);
            }
            IndirectAddress::RipGlobal(_) => {}
        }
    };

    (RegMem, $e:expr, $collector:expr) => {
        match $e {
            RegMem::Reg(r) => $collector.push(r),
            RegMem::Mem(loc) => {
                push_if_reg!(IndirectAddress, loc, $collector);
            }
        }
    };

    (RegImm, $e:expr, $collector:expr) => {
        match $e {
            RegImm::Reg(r) => $collector.push(r),
            RegImm::Imm(_) => {}
        }
    };
}

impl MachInst<X86_64> for Inst {
    fn uses<const N: usize>(&self, collector: &mut RegCollector<N>) {
        match self {
            Inst::Nop(_) => {}
            Inst::Mov(mov) => {
                push_if_reg!(RegMemImm, mov.src, collector);
            }
            Inst::MovStore(mov) => {
                push_if_reg!(RegImm, mov.src, collector);
                push_if_reg!(IndirectAddress, mov.dest, collector);
            }
            Inst::ALU(alu) => {
                push_if_reg!(RegMemImm, alu.rhs, collector);
                collector.push(alu.lhs.to_reg());
            }
            Inst::Not(not) => {
                collector.push(not.reg.to_reg());
            }
            Inst::Neg(neg) => {
                collector.push(neg.reg.to_reg());
            }
            Inst::IMul(mul) => {
                push_if_reg!(RegMemImm, mul.rhs, collector);
                collector.push(mul.lhs.to_reg());
            }
            Inst::Cmp(cmp) => {
                push_if_reg!(RegMemImm, cmp.rhs, collector);
                collector.push(cmp.lhs);
            }
            Inst::Test(test) => {
                push_if_reg!(RegMemImm, test.rhs, collector);
                collector.push(test.lhs);
            }
            Inst::Set(_) => {}
            Inst::Push(push) => {
                collector.push(push.value);
            }
            Inst::Pop(_) => {}
            Inst::Movabs(_) => {}
            Inst::Cwd(cwd) => {
                collector.push(cwd.src);
            }
            Inst::Cdq(cdq) => {
                collector.push(cdq.src);
            }
            Inst::Cqo(cqo) => {
                collector.push(cqo.src);
            }
            Inst::Div(div) => {
                push_if_reg!(RegMem, div.divisor, collector);
                collector.push(Div::DIVIDEND_LO);
                collector.push(Div::DIVIDEND_HI);
            }
            Inst::IDiv(idiv) => {
                push_if_reg!(RegMem, idiv.divisor, collector);
                collector.push(IDiv::DIVIDEND_LO);
                collector.push(IDiv::DIVIDEND_HI);
            }
            Inst::Call(_) => {}
            Inst::IndirectCall(call) => {
                push_if_reg!(RegMemImm, call.func, collector);
            }
            Inst::Jump(_) => {}
            Inst::Ret(_) => {}
            Inst::Ud2(_) => {}
        }
    }

    fn defs<const N: usize>(&self, collector: &mut RegCollector<N>) {
        match self {
            Inst::Nop(_) => {}
            Inst::Mov(mov) => {
                collector.push(mov.dest.to_reg());
            }
            Inst::MovStore(_) => {}
            Inst::ALU(alu) => {
                collector.push(alu.lhs.to_reg());
            }
            Inst::Not(not) => {
                collector.push(not.reg.to_reg());
            }
            Inst::Neg(neg) => {
                collector.push(neg.reg.to_reg());
            }
            Inst::IMul(mul) => {
                collector.push(mul.lhs.to_reg());
                collector.push(mul.dest_hi.to_reg());
            }
            Inst::Cmp(_) => {}
            Inst::Test(_) => {}
            Inst::Set(set) => {
                collector.push(set.dest.to_reg());
            }
            Inst::Push(_) => {}
            Inst::Pop(pop) => {
                collector.push(pop.dest.to_reg());
            }
            Inst::Movabs(movabs) => {
                collector.push(movabs.dest.to_reg());
            }
            Inst::Cwd(cwd) => {
                collector.push(cwd.dest.to_reg());
            }
            Inst::Cdq(cdq) => {
                collector.push(cdq.dest.to_reg());
            }
            Inst::Cqo(cqo) => {
                collector.push(cqo.dest.to_reg());
            }
            Inst::Div(div) => {
                collector.push(Div::QUOTIENT);
                collector.push(Div::REMAINDER);
            }
            Inst::IDiv(idiv) => {
                collector.push(IDiv::QUOTIENT);
                collector.push(IDiv::REMAINDER);
            }
            Inst::Call(_) => {}
            Inst::IndirectCall(_) => {}
            Inst::Jump(_) => {}
            Inst::Ret(_) => {}
            Inst::Ud2(_) => {}
        }
    }

    fn is_move(&self) -> bool {
        match self {
            Self::Mov(mov) => matches!(mov.src, RegMemImm::Reg(_)),
            _ => false,
        }
    }

    fn as_move(self) -> Option<Move> {
        match self {
            Self::Mov(mov) => match mov.src {
                RegMemImm::Reg(src) => Some(Move {
                    width: mov.width.into_bytes(),
                    to: mov.dest,
                    from: src,
                }),
                _ => None,
            },
            _ => None,
        }
    }

    fn mov(width: usize, src: Reg, dest: WriteableReg) -> Self {
        Self::Mov(Mov {
            width: Width::from_bytes(width),
            src: RegMemImm::Reg(src),
            dest,
        })
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
