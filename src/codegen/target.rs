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
use crate::codegen::x86_64::{
    Debug3RegLinuxX86_64, LinuxX86_64, MacOSX86_64, WindowsX86_64, X86_64,
};
use crate::codegen::{CallingConv, CodegenOptions, MachInst, StackFrame};
use crate::ir::{FloatFormat, Function, Module, Type, TypePool, UType};
use crate::utility::SaHashMap;
use std::fmt;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::str::FromStr;

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
    X86_64Windows,
    /// 64-bit arm Linux
    Aarch64Linux,
    /// 64-bit arm macOS
    Arm64macOS,
    /// 64-bit arm Windows
    Arm64Windows,
    /// A test 3-register target that is identical to [`Self::X86_64Linux`] in every
    /// way observable, except that only the registers `r8`, `r9`, and `r10` are
    /// available for the register allocator to use.
    Debug3Reg,
}

impl FromStr for TargetPair {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "x86_64-linux" => Ok(TargetPair::X86_64Linux),
            "x86_64-mac" => Ok(TargetPair::X86_64macOS),
            "x86_64-win" => Ok(TargetPair::X86_64Windows),
            "aarch64-linux" => Ok(TargetPair::Aarch64Linux),
            "arm64-mac" => Ok(TargetPair::Arm64macOS),
            "arm64-win" => Ok(TargetPair::Arm64Windows),
            "debug3reg" => Ok(TargetPair::Debug3Reg),
            _ => {
                Err("the available targets are `x86_64-linux`, `x86_64-mac`, `x86_64-win`, `aarch64-linux`, `arm64-mac`, `arm64-win`, `debug3reg`")
            }
        }
    }
}

impl fmt::Display for TargetPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TargetPair::X86_64Linux => write!(f, "x86_64-linux"),
            TargetPair::X86_64macOS => write!(f, "x86_64-mac"),
            TargetPair::X86_64Windows => write!(f, "x86_64-win"),
            TargetPair::Aarch64Linux => write!(f, "aarch64-linux"),
            TargetPair::Arm64macOS => write!(f, "arm64-mac"),
            TargetPair::Arm64Windows => write!(f, "arm64-win"),
            TargetPair::Debug3Reg => write!(f, "debug4reg"),
        }
    }
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
            pub const fn identity(self) -> usize {
                self.data as usize
            }

            /// Gets the physical "number" of the register that identifies it **within the
            /// class of that register**. This value may overlap with other register classes.
            #[inline]
            pub const fn hw_number(self) -> usize {
                (self.data >> 1) as usize
            }

            /// Gets what type of register this register is for.
            #[inline]
            pub const fn class(self) -> RegClass {
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

    /// Gets the register class of the underlying register, regardless of whether
    /// the underlying register is a virtual register or physical register.
    #[inline]
    pub const fn class(self) -> RegClass {
        if self.is_preg() {
            (PReg {
                data: (self.data >> 1) as u8,
            })
            .class()
        } else {
            (VReg {
                data: self.data >> 1,
            })
            .class()
        }
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
    /// The MIR instruction type used for the architecture
    type Inst: MachInst<Arch = Self>;

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

/// Models the idea of a "platform," i.e. a target operating environment that
/// code is being generated for.
///
/// This mostly deals with ABI shenanigans for the code generator.
pub trait Platform<Arch: Architecture>: Debug {
    /// Returns an instance of the default calling convention for the platform.
    fn default_calling_convention(&self) -> &'static dyn CallingConv<Arch>;

    /// Creates an instance of the default stack frame object for the platform,
    /// preconfiguring it for `func`.
    fn default_stack_frame(
        &self,
        func: &Function,
        target: &Target<Arch>,
    ) -> Box<dyn StackFrame<Arch>>;
}

/// Models the data-layout, calling conventions and other details necessary
/// for generating code for a specific architecture and ABI.
#[derive(Debug)]
pub struct Target<Arch: Architecture> {
    platform: Box<dyn Platform<Arch>>,
    aggregate_type_layouts: SaHashMap<Type, TypeLayout>,
    options: CodegenOptions,
    _unused: PhantomData<fn() -> Arch>,
}

impl<Arch: Architecture> Target<Arch> {
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

    /// Gets a new stack frame for a given function
    #[inline]
    pub fn new_frame(&self, func: &Function) -> Box<dyn StackFrame<Arch>> {
        self.platform.default_stack_frame(func, self)
    }

    /// Gets a new calling convention for a given function
    #[inline]
    pub fn new_callcc(&self) -> &'static dyn CallingConv<Arch> {
        self.platform.default_calling_convention()
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

    /// Gets the [`CodegenOptions`] that the code is being generated according to.
    #[inline]
    pub fn options(&self) -> CodegenOptions {
        self.options
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
    /// Returns a [`Target`] that is configured for the x86-64 System V ABI
    /// on Linux-based operating systems.
    #[inline]
    pub fn linux_x86_64(options: CodegenOptions) -> Target<X86_64> {
        Target {
            options,
            platform: Box::new(LinuxX86_64),
            aggregate_type_layouts: SaHashMap::default(),
            _unused: PhantomData,
        }
    }

    /// Returns a [`Target`] that is configured for the x86-64 System V ABI
    /// on x86-64 macOS.
    #[inline]
    pub fn mac_os_x86_64() -> Target<X86_64> {
        Target {
            options: CodegenOptions {
                omit_frame_pointer: false,
            },
            platform: Box::new(MacOSX86_64),
            aggregate_type_layouts: SaHashMap::default(),
            _unused: PhantomData,
        }
    }

    /// Returns a [`Target`] that is configured for the x86-64 Windows ABI
    /// and is targeting x86-64 Windows.
    #[inline]
    pub fn windows_x86_64(options: CodegenOptions) -> Target<X86_64> {
        Target {
            options,
            platform: Box::new(WindowsX86_64),
            aggregate_type_layouts: SaHashMap::default(),
            _unused: PhantomData,
        }
    }

    /// Returns a [`Target`] that is configured for the 3-register debugging target.
    #[inline]
    pub fn debug_3reg(options: CodegenOptions) -> Target<X86_64> {
        Target {
            options,
            platform: Box::new(Debug3RegLinuxX86_64),
            aggregate_type_layouts: SaHashMap::default(),
            _unused: PhantomData,
        }
    }
}
