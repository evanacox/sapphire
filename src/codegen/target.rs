//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::ArenaKey;
use crate::codegen::x86_64::{IndirectAddress, RegMemImm, SystemV, WindowsX64, X86_64};
use crate::codegen::MachInst;
use crate::ir::{FloatFormat, Module, Signature, StackSlot, Type, TypePool, UType};
use crate::utility::SaHashMap;
use std::marker::PhantomData;

/// Models the specific CPU architecture that is being targeted.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum CPUArch {
    /// The 64-bit extension to x86, also known as `amd64`.
    X86_64,
    /// The 64-bit extension to arm, also known as `arm64`
    Aarch64,
}

/// Supported CPU/OS targets. These are associated with their default ABIs
/// on the platforms being referred to.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum TargetPair {
    /// 64-bit x86 Linux
    X86_64Linux,
    /// 64-bit x86 macOS
    X86_64macOS,
    /// 64-bit x86 Windows
    X64Windows,
    /// 64-bit arm Linux
    Aarch64Linux,
    /// 64-bit arm macOS
    Arm64macOS,
    /// 64-bit arm Windows
    Arm64Windows,
}

/// Models the layout of a given type. This is the size and alignment requirements
/// of the type, if the size/alignment/offset of subfields is desired you either need to
/// get the layout of that subfield's type, or use the [`AggregateLayout::offset`] API.
///
/// [`AggregateLayout::offset`]: crate::codegen::AggregateLayout::offset
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct TypeLayout(u64, u64);

impl TypeLayout {
    pub(crate) const fn new(size: u64, align: u64) -> Self {
        Self(size, align)
    }

    /// The number of contiguous bytes required to store a value of type `T`.
    ///
    /// This is equivalent to the result of `sizeof` in C.
    pub fn size(&self) -> u64 {
        self.0
    }

    /// The number of bytes that a given section of memory must be aligned to in order to
    /// store a value of type `T`.
    ///
    /// This is equivalent to the result of `alignof`/`_Alignof` in C.
    pub fn align(&self) -> u64 {
        self.1
    }
}

/// Models the type of register that a given register is.
///
/// As of right now, this is only an integer or a float register.
#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum RegClass {
    /// The register class for integer values.
    Int = 0,
    /// The register class for floating-point values.
    Float = 1,
}

macro_rules! generic_reg {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident($ty:ty); $($rest:tt)* ) => {
        $(#[$outer])*
        #[repr(transparent)]
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        #[cfg_attr(feature = "enable-serde", derive(serde::Serialize, serde::Deserialize))]
        $vis struct $name {
            data: $ty
        }

        impl $name {
            /// Creates a register with a given number and class
            #[inline]
            pub const fn with_class(class: RegClass, hw_number: usize) -> Self {
                Self {
                    data: ((hw_number as $ty) << 1) | (class as $ty)
                }
            }

            /// Creates an integer register with a given hardware number
            #[inline]
            pub const fn int(hw_number: usize) -> Self {
                Self::with_class(RegClass::Int, hw_number)
            }

            /// Creates a floating-point register with a given hardware number
            #[inline]
            pub const fn float(hw_number: usize) -> Self {
                Self::with_class(RegClass::Float, hw_number)
            }

             /// The "index" of the register. This is effectively the identity of the
             /// physical register itself, no other physical register will have the same index.
             ///
             /// This is intended for usage in storing registers in an array.
            #[inline]
            pub fn identity(self) -> usize {
                self.data as usize
            }

            /// Gets the physical "number" of the register that identifies it **within the
            /// class of that register**. This value may overlap with other register classes.
            #[inline]
            pub fn hw_number(self) -> usize {
                (self.data >> 1) as usize
            }

            /// Gets what type of register this register is for.
            #[inline]
            pub fn class(self) -> RegClass {
                if self.data & 1 == 0 {
                    RegClass::Int
                } else {
                    RegClass::Float
                }
            }
        }


        impl ArenaKey for $name {
            type Item = $ty;

            #[inline]
            fn key_new(index: usize) -> Self {
                Self {
                    data: index as $ty,
                }
            }

            #[inline]
            fn key_index(self) -> usize {
                self.identity()
            }
        }

        generic_reg!($($rest)*);
    };

    () => {}
}

generic_reg! {
    /// Represents a single physical register on a CPU. The register class
    /// is stored in one bit, while the register number is in the other bits
    /// that are below that bit.
    pub struct PReg(u8);

    /// Represents a single **virtual** register. The register class
    /// is stored in one bit, while the register number is in the other bits
    /// that are below that bit.
    ///
    /// Unlike a physical register, this is not bounded by the constraints of
    /// any hardware.
    pub struct VReg(u32);
}

/// A register that is either a virtual register or a physical register of
/// a given register class.
///
/// This stores either a [`VReg`] or a [`PReg`] in the upper 31 bits of its
/// data, with a discriminator in the lowest bit. This prevents issues with
/// using [`Reg`] values as arena keys, because if it was the highest bit
/// it would break secondary maps.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct Reg {
    data: u32,
}

impl Reg {
    /// Creates a new [`Reg`] from a physical register.
    #[inline]
    pub const fn from_preg(reg: PReg) -> Self {
        Self {
            // lsb is 0, signals preg
            data: (reg.data as u32) << 1,
        }
    }

    /// Creates a new [`Reg`] from a virtual register.
    #[inline]
    pub const fn from_vreg(reg: VReg) -> Self {
        Self {
            // lsb is 1, signals vreg
            data: (reg.data << 1) | 1,
        }
    }

    /// If `self` is a [`VReg`], returns it.
    #[inline]
    pub const fn as_vreg(self) -> Option<VReg> {
        if self.is_vreg() {
            Some(VReg {
                data: self.data >> 1,
            })
        } else {
            None
        }
    }

    /// If `self` is a [`PReg`], returns it.
    #[inline]
    pub const fn as_preg(self) -> Option<PReg> {
        if self.is_preg() {
            Some(PReg {
                data: (self.data >> 1) as u8,
            })
        } else {
            None
        }
    }

    /// Checks if `self` is a [`VReg`]
    #[inline]
    pub const fn is_vreg(self) -> bool {
        self.data & 1 != 0
    }

    /// Checks if `self` is a [`PReg`]
    #[inline]
    pub const fn is_preg(self) -> bool {
        !self.is_vreg()
    }
}

impl ArenaKey for Reg {
    type Item = u8;

    #[inline]
    fn key_new(index: usize) -> Self {
        Self { data: index as u32 }
    }

    #[inline]
    fn key_index(self) -> usize {
        self.data as usize
    }
}

/// A new-type for a register that is writeable. This doesn't actually enforce anything
/// but makes assumptions obvious in the code since the conversion is explicit.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct WriteableReg(Reg);

impl WriteableReg {
    /// Converts a [`Reg`] into a [`WriteableReg`]. In doing so, the caller is
    /// saying that they know that a register is writeable.
    pub fn from_reg(reg: Reg) -> Self {
        Self(reg)
    }

    /// Converts a [`WriteableReg`] back a [`Reg`]. In doing so, the caller knows
    /// that the returned register is writeable.
    pub fn to_reg(self) -> Reg {
        self.0
    }
}

impl ArenaKey for WriteableReg {
    type Item = u8;

    #[inline]
    fn key_new(index: usize) -> Self {
        Self(Reg::key_new(index))
    }

    #[inline]
    fn key_index(self) -> usize {
        self.0.key_index()
    }
}

/// Models the architecture-specific details that a backend needs to deal with,
/// mainly fundamental type layouts.
pub trait Architecture {
    /// Returns the specific CPU architecture this is configured for
    fn cpu() -> CPUArch;

    /// Returns the layout of a `bool`
    fn bool_layout() -> TypeLayout;

    /// Returns the layout of a `ptr`
    fn ptr_layout() -> TypeLayout;

    /// Returns the layout of an `i8`
    fn i8_layout() -> TypeLayout;

    /// Returns the layout of an `i16`
    fn i16_layout() -> TypeLayout;

    /// Returns the layout of an `i32`
    fn i32_layout() -> TypeLayout;

    /// Returns the layout of an `i64`
    fn i64_layout() -> TypeLayout;

    /// Returns the layout of an `f32`
    fn f32_layout() -> TypeLayout;

    /// Returns the layout of an `f64`
    fn f64_layout() -> TypeLayout;

    /// Returns a list of all the accessible registers for the architecture
    fn physical_regs() -> &'static [PReg];

    /// Gets the register that refers to the instruction pointer
    fn instruction_pointer() -> PReg;
}

/// Details about a specific target ABI necessary for code generation.
pub trait ABI<A: Architecture> {
    /// A builder that handles calling convention shenanigans for a single call.
    ///
    /// This allows instruction selection code to just delegate to the builder for
    /// the ABI-specific details of calling a function.
    type CallingConvBuilder;

    /// Models the stack frame for a function.
    type FrameInfo;

    /// Returns a list of all the registers that are preserved by the **caller** of
    /// a function. These are also known as "volatile" registers in some ABIs.
    ///
    /// If a function calls another and needs to maintain values in these registers,
    /// they must be preserved somehow.
    fn callee_preserved() -> &'static [PReg];

    /// Returns a list of all the registers that are preserved by the **callee**
    /// of a function. These are known as "non-volatile" registers in some ABIs.
    ///
    /// If a function needs to modify these, they must preserve
    /// their values first and restore them before returning.
    fn caller_preserved() -> &'static [PReg];

    /// Gets the frame pointer register for the ABI
    fn frame_pointer() -> PReg;

    /// Gets the `sp` register for the ABI
    fn stack_pointer() -> PReg;

    /// Returns the required stack alignment for a function call to be performed.
    fn stack_alignment() -> u64;

    /// Returns a builder that can help place parameters in the correct places for a call
    fn start_call() -> Self::CallingConvBuilder;

    /// Gets a new frame for the current function
    fn new_frame(sig: &Signature) -> Self::FrameInfo;

    /// Checks if a type can be passed in registers or not.
    fn can_pass_in_registers(pool: &TypePool, ty: Type, layout: TypeLayout) -> bool;
}

/// The location of a single "variable." This denotes something at the ABI level,
/// e.g. `stackslot`s, parameters and the like. This identifies where they are
/// in a way that the code generator can understand.
pub enum VariableLocation<Arch, Abi>
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    /// Says that a variable is located in a register
    InReg(Reg),
    /// Says that a variable is located at an offset relative to the frame pointer
    RelativeToFP(i32, PhantomData<fn() -> (Arch, Abi)>),
    /// Says that a variable is located at an offset relative to the stack pointer
    RelativeToSP(i32, PhantomData<fn() -> (Arch, Abi)>),
}

impl<Arch, Abi> From<VariableLocation<Arch, Abi>> for RegMemImm
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    fn from(value: VariableLocation<Arch, Abi>) -> Self {
        match value {
            VariableLocation::InReg(reg) => Self::Reg(reg),
            VariableLocation::RelativeToFP(offset, _) => Self::Mem(IndirectAddress::RegOffset(
                Reg::from_preg(Abi::frame_pointer()),
                offset,
            )),
            VariableLocation::RelativeToSP(offset, _) => Self::Mem(IndirectAddress::RegOffset(
                Reg::from_preg(Abi::stack_pointer()),
                offset,
            )),
        }
    }
}

/// Interface for a generic "stack frame" that a target can implement. This is used by the code generator
/// to place data in the correct place at the function level.
///
/// This is a stateful type, the code generator
pub trait Frame<Inst: MachInst<Self::Arch>> {
    /// The architecture that the frame is for
    type Arch: Architecture;

    /// The ABI that the frame is for
    type Abi: ABI<Self::Arch>;

    /// Creates a new stack frame with nothing in it
    fn new(sig: &Signature) -> Self;

    /// Creates a stack slot, returning a location that it goes to
    fn stack_slot(&mut self, stack: StackSlot) -> VariableLocation<Self::Arch, Self::Abi>;
}

/// Models the data-layout, calling conventions and other details necessary
/// for generating code for a specific architecture and ABI.
#[derive(Clone, Debug)]
pub struct Target<Arch, Abi>
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    aggregate_type_layouts: SaHashMap<Type, TypeLayout>,
    _unused: PhantomData<fn() -> (Arch, Abi)>,
}

impl<Arch, Abi> Target<Arch, Abi>
where
    Arch: Architecture,
    Abi: ABI<Arch>,
{
    /// Calculates all the type layouts for every type present in a given module.
    ///
    /// This must be called before the target can be queried for the layouts of
    /// arbitrary types.
    pub fn prepare_for(&mut self, module: &Module) {
        let pool = module.type_pool();

        for ty in pool.all_types() {
            let _ = self.calculate_layout(&pool, ty);
        }
    }

    /// Gets the [`TypeLayout`] associated with a given type.
    #[inline]
    pub fn layout_of(&self, ty: Type) -> TypeLayout {
        self.maybe_layout_of(ty)
            .unwrap_or_else(|| self.aggregate_type_layouts[&ty])
    }

    /// Returns the specific CPU architecture this is configured for
    #[inline]
    pub fn cpu(&self) -> CPUArch {
        Arch::cpu()
    }

    /// Returns a list of all the accessible registers for the architecture
    #[inline]
    pub fn physical_regs(&self) -> &'static [PReg] {
        Arch::physical_regs()
    }

    /// Gets the register that refers to the instruction pointer
    #[inline]
    pub fn instruction_pointer(&self) -> PReg {
        Arch::instruction_pointer()
    }

    /// Returns a list of all the registers that are preserved by the **caller** of
    /// a function. These are also known as "volatile" registers in some ABIs.
    ///
    /// If a function calls another and needs to maintain values in these registers,
    /// they must be preserved somehow.
    #[inline]
    pub fn callee_preserved() -> &'static [PReg] {
        Abi::callee_preserved()
    }

    /// Returns a list of all the registers that are preserved by the **callee**
    /// of a function. These are known as "non-volatile" registers in some ABIs.
    ///
    /// If a function needs to modify these, they must preserve
    /// their values first and restore them before returning.
    #[inline]
    pub fn caller_preserved() -> &'static [PReg] {
        Abi::caller_preserved()
    }

    /// Returns the required stack alignment for a function call to be performed.
    #[inline]
    pub fn stack_alignment(&self) -> u64 {
        Abi::stack_alignment()
    }

    /// Returns a builder that can help place parameters in the correct places for a call
    #[inline]
    pub fn start_call(&self) -> Abi::CallingConvBuilder {
        Abi::start_call()
    }

    fn maybe_layout_of(&self, ty: Type) -> Option<TypeLayout> {
        match ty.unpack() {
            UType::Bool(_) => Some(Arch::bool_layout()),
            UType::Ptr(_) => Some(Arch::ptr_layout()),
            UType::Int(ty) => Some(match ty.width() {
                8 => Arch::i8_layout(),
                16 => Arch::i16_layout(),
                32 => Arch::i32_layout(),
                64 => Arch::i64_layout(),
                _ => unreachable!(),
            }),
            UType::Float(ty) => Some(match ty.format() {
                FloatFormat::Single => Arch::f32_layout(),
                FloatFormat::Double => Arch::f64_layout(),
            }),
            _ => None,
        }
    }

    fn calculate_layout(&mut self, pool: &TypePool, ty: Type) -> TypeLayout {
        let result = match ty.unpack() {
            UType::Array(arr) => {
                let element_ty = arr.element(pool);
                let size = arr.len(pool);
                let inner = self
                    .maybe_layout_of(element_ty)
                    .unwrap_or_else(|| self.calculate_layout(pool, element_ty));

                TypeLayout::new(inner.size() * size, inner.align())
            }
            UType::Struct(_) => {
                todo!()
            }
            _ => unreachable!(),
        };

        self.aggregate_type_layouts.insert(ty, result);

        result
    }
}

/// Preset target configurations for specific architecture/ABI sets.
pub struct PresetTargets;

impl PresetTargets {
    /// Returns a [`Target`] that is configured for the x86_64 System V ABI.
    ///
    /// This is suitable for x86_64 Linux and macOS.
    #[inline]
    pub fn sys_v() -> Target<X86_64, SystemV> {
        Target {
            aggregate_type_layouts: SaHashMap::default(),
            _unused: PhantomData::default(),
        }
    }

    /// Returns a [`Target`] that is configured for the x86_64 Windows ABI.
    ///
    /// This is suitable for x86_64 Windows.
    #[inline]
    pub fn win64() -> Target<X86_64, WindowsX64> {
        Target {
            aggregate_type_layouts: SaHashMap::default(),
            _unused: PhantomData::default(),
        }
    }
}
