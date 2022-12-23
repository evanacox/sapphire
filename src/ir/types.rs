//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::UniqueArenaMap;
use crate::arena_key;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use static_assertions::assert_eq_size;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

arena_key! {
    // we rely more directly on the `u32` assumption here,
    // so we don't use `dense_arena_key`. other code only relies
    // on it implicitly (e.g. size constraints), this code relies on
    // being able to transmute from/to u32
    struct CompoundTypeRef(u32);
}

#[repr(usize)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
enum CompoundTypeData {
    Array(Type, usize),
    Struct(Vec<Type>),
}

assert_eq_size!(CompoundTypeData, [usize; 4]);

/// Manages all of the compound types for a given module of IR.
///
/// Some types (structs and arrays) are possibly self-referential and therefore
/// require some sort of indirection, but at the same time we don't want to bloat
/// up normal [`Type`] objects that are usually just integers. This manages
/// the compound types in place of making [`Type`] do it, and [`Type`] instead
/// refers into this context for those larger types.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct TypeContext {
    arena: UniqueArenaMap<CompoundTypeRef, CompoundTypeData>,
}

impl TypeContext {
    /// Constructs a new, empty [`TypeContext`].
    pub fn new() -> Self {
        Self {
            arena: UniqueArenaMap::default(),
        }
    }

    /// Creates an array type, and returns a [`Type`] that refers to that array type.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let t1 = Type::ptr();
    /// let t2 = ctx.array(t1, 512); // [ptr; 512]
    /// assert_eq!(t2.is_array(), true);
    /// ```
    pub fn array(&mut self, inner: Type, len: usize) -> Type {
        let data = CompoundTypeData::Array(inner, len);
        let key = self.arena.insert(data);

        Type::array_from_ref(key)
    }

    /// Creates a struct type, and returns a [`Type`] that refers to that struct type.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let ty = ctx.structure(&[Type::ptr(), Type::i64(), Type::i64()]); // [ptr; 512]
    /// assert_eq!(ty.is_struct(), true);
    /// ```
    pub fn structure(&mut self, fields: &[Type]) -> Type {
        let data = CompoundTypeData::Struct(Vec::from(fields));
        let key = self.arena.insert(data);

        Type::struct_from_ref(key)
    }

    #[inline]
    fn data_of(&self, key: CompoundTypeRef) -> &CompoundTypeData {
        &self.arena[key]
    }
}

impl Default for TypeContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Models a boolean type in the IR.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Bool(());

/// Models a pointer type in the IR.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Ptr(());

/// Models the `iN` class of fundamental types.
///
/// Integers are in the form `iN`, such that $N \in \\{8, 16, 32, 64\\}$. Other
/// bit widths are currently unsupported by the library.
///
/// ```
/// # use sapphire::ir::*;
/// let t1 = Type::i8().unwrap_int();
/// assert_eq!(t1.width(), 8);
/// assert_eq!(t1.mask(), 0xFF);
/// assert_eq!(t1.sign_bit(), 0b1000_0000);
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Int {
    width: u32,
}

impl Int {
    #[inline]
    const fn of_width_unchecked(bit_width: u32) -> Self {
        Self { width: bit_width }
    }

    /// Gets the width of the integer.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let ty = Type::int(64);
    /// assert_eq!(ty.unwrap_int().width(), 64);
    /// ```
    #[inline]
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Returns a mask with the sign bit (MSB in 2's complement) set for
    /// an integer of `self.width()` width.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i32().unwrap_int();
    /// let t2 = Type::i8().unwrap_int();
    ///
    /// assert_eq!(t1.sign_bit(), 0x80000000);
    /// assert_eq!(t2.sign_bit(), 0b1000_0000);
    /// ```
    #[inline]
    pub fn sign_bit(&self) -> u64 {
        1u64 << ((self.width() as u64) - 1)
    }

    /// Returns a mask with every usable bit in the type set. This equivalent
    /// to the value resulting from the instruction `xor iN $x, -1`
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i64().unwrap_int();
    /// let t2 = Type::i16().unwrap_int();
    ///
    /// assert_eq!(t1.mask(), 0xFFFFFFFFFFFFFFFF);
    /// assert_eq!(t2.mask(), 0b1111_1111_1111_1111);
    /// ```
    #[inline]
    pub fn mask(&self) -> u64 {
        !0u64 >> (64u64 - self.width() as u64)
    }

    /// Checks if the integer type has a width of 8.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i8().unwrap_int();
    /// assert_eq!(t1.is_i8(), true);
    ///
    /// let t2 = Type::i32().unwrap_int();
    /// assert_eq!(t2.is_i8(), false);
    /// ```
    #[inline]
    pub const fn is_i8(&self) -> bool {
        self.width == 8
    }

    /// Checks if the integer type has a width of 16.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i16().unwrap_int();
    /// assert_eq!(t1.is_i16(), true);
    ///
    /// let t2 = Type::i64().unwrap_int();
    /// assert_eq!(t2.is_i16(), false);
    /// ```
    #[inline]
    pub const fn is_i16(&self) -> bool {
        self.width == 16
    }

    /// Checks if the integer type has a width of 32.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i32().unwrap_int();
    /// assert_eq!(t1.is_i32(), true);
    ///
    /// let t2 = Type::i16().unwrap_int();
    /// assert_eq!(t2.is_i32(), false);
    /// ```
    #[inline]
    pub const fn is_i32(&self) -> bool {
        self.width == 32
    }

    /// Checks if the integer type has a width of 64.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i64().unwrap_int();
    /// assert_eq!(t1.is_i64(), true);
    ///
    /// let t2 = Type::i8().unwrap_int();
    /// assert_eq!(t2.is_i64(), false);
    /// ```
    #[inline]
    pub const fn is_i64(&self) -> bool {
        self.width == 64
    }
}

/// Maps the hardware representation of the floating-point types
/// to enum variants.
///
/// These map directly to types defined in the IEEE-754 standard.
#[repr(u32)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, FromPrimitive)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum FloatFormat {
    /// Models `f32`, an IEEE single-precision float (`binary32`).
    Single,
    /// Models `f64`, an IEEE double-precision float (`binary64`).
    Double,
}

/// Models the `fN` class of fundamental types.
///
/// Floats are in the form `fN`, such that $N \in \\{32, 64\\}$. They follow
/// the IEEE-754 standard, so `f32` is an IEEE Single and `f64` is an IEEE Double.
///
/// See `fN` in the [Reference](https://pages.evanacox.io/sapphire/sir/reference#fn-floats).
///
/// ```
/// # use sapphire::ir::*;
/// let t1 = Type::float(FloatFormat::Single);
/// let t2 = Type::f32();
/// assert_eq!(t1, t2);
/// ```
#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Float {
    real: FloatFormat,
}

impl Float {
    #[inline]
    pub(in crate::ir) const fn new(real: FloatFormat) -> Self {
        Self { real }
    }

    /// Gets the underlying IEEE floating-point type from a given `fN` type
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::float(FloatFormat::Single);
    /// assert_eq!(t1.unwrap_float().format(), FloatFormat::Single);
    /// ```
    #[inline]
    pub const fn format(self) -> FloatFormat {
        self.real
    }
}

/// Models an array type in the IR. Internally, contains a reference into
/// the [`TypeContext`] that is being used for the module being operated on.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Array {
    inner: CompoundTypeRef,
}

impl Array {
    /// Looks into the type context and returns the length of the array.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let t1 = Type::array(&mut ctx, Type::i32(), 16);
    /// assert_eq!(t1.unwrap_array().len(&ctx), 16);
    /// ```
    #[inline]
    #[allow(clippy::len_without_is_empty)] // broken check, freaks out over `is_empty` sig but not this one's sig
    pub fn len(&self, ctx: &TypeContext) -> usize {
        self.data(ctx).1
    }

    /// Looks into the type context and checks if the array length is `0`.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let t1 = Type::array(&mut ctx, Type::i32(), 16);
    /// assert_eq!(t1.unwrap_array().is_empty(&ctx), false);
    /// ```
    #[inline]
    pub fn is_empty(&self, ctx: &TypeContext) -> bool {
        self.len(ctx) == 0
    }

    /// Looks into the type context and returns the length of the array.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let t1 = Type::array(&mut ctx, Type::i32(), 16);
    /// assert_eq!(t1.unwrap_array().element(&ctx), Type::i32());
    /// ```
    #[inline]
    pub fn element(&self, ctx: &TypeContext) -> Type {
        self.data(ctx).0
    }

    #[inline]
    fn data(&self, ctx: &TypeContext) -> (Type, usize) {
        match ctx.data_of(self.inner) {
            CompoundTypeData::Array(ty, len) => (*ty, *len),
            _ => unreachable!(),
        }
    }
}

/// Models a structure type in the IR. Internally, contains a reference into
/// the [`TypeContext`] that is being used for the module being operated on.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Struct {
    inner: CompoundTypeRef,
}

impl Struct {
    /// Looks into the type context and gets the fields of the struct
    /// out of it.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// use sapphire::ir::TypeContext;
    /// let mut ctx = TypeContext::new();
    /// let ty = Type::structure(&mut ctx, &[Type::ptr(), Type::i64(), Type::i64()]);
    /// assert_eq!(*ty.unwrap_struct().members(&ctx), [Type::ptr(), Type::i64(), Type::i64()]);
    /// ```
    #[inline]
    pub fn members<'a>(&self, ctx: &'a TypeContext) -> &'a [Type] {
        match ctx.data_of(self.inner) {
            CompoundTypeData::Struct(v) => v,
            _ => &[],
        }
    }
}

/// A reference to a type. Copyable, compact, lightweight, and can model arbitrary
/// types in the IR.
///
/// This type either contains all the information about the type (in the case of
/// fundamental types), or contains a reference into a [`TypeContext`] that holds
/// the information about the type (only for arrays and structures).
///
/// ```
/// # use sapphire::ir::*;
/// let t1 = Type::bool(); // models `bool`
/// let t2 = Type::ptr(); // models `ptr`
/// assert_ne!(t1, t2);
/// ```
///
/// For better pattern-matching it must be unpacked into an [`UType`]
/// that has an actual `enum` representation, note that [`UType`] is
/// the size of `(u32, u32)` instead of `u32`.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Type {
    // representation:
    //
    //     [ x x x x x x x x x x x x x x x x x x x x x x x x x x x x x A A A ]
    //                                                                 ~~~~~ - discriminator
    //
    //       --------------------------------------------------------- - other data
    //
    raw: u32,
}

macro_rules! int_shorthand {
    ($lower:ident, $n:tt) => {
        #[doc = concat!("Shorthand for creating an integer of width `", stringify!($n), "`.")]
        #[doc = concat!("Exactly equivalent to `Type::int(", stringify!($n), ")`.")]
        #[doc = ""]
        #[doc = "```"]
        #[doc = "# use sapphire::ir::Type;"]
        #[doc = concat!("let t1 = Type::i", stringify!($n), "();")]
        #[doc = concat!("let t2 = Type::int(", stringify!($n), ");")]
        #[doc = ""]
        #[doc = "assert_eq!(t1, t2);"]
        #[doc = "```"]
        pub const fn $lower() -> Self {
            Self::int($n)
        }
    };
}

impl Type {
    const BOOL: u32 = 0b000;

    const PTR: u32 = 0b001;

    const INT: u32 = 0b010;

    const FLOAT: u32 = 0b011;

    const ARRAY: u32 = 0b100;

    const STRUCT: u32 = 0b101;

    const DATA_SHIFT: u32 = 3;

    const DATA_MASK: u32 = (!0) << Self::DATA_SHIFT;

    const DISCRIMINATOR_MASK: u32 = 0b111;

    /// Creates a boolean type (the `bool` type in the IR).
    pub const fn bool() -> Self {
        Self { raw: Self::BOOL }
    }

    /// Creates a pointer type (the `ptr` type in the IR).
    pub const fn ptr() -> Self {
        Self { raw: Self::PTR }
    }

    /// Creates an integer type (the `iN` types in the IR) with a given
    /// width. Given `width` is $$N$$, $$N \in {8,16,32,64}$$ must be true.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::int(32);
    /// let t2 = Type::int(64);
    /// assert_ne!(t1, t2);
    /// ```
    pub const fn int(width: u32) -> Self {
        debug_assert!(width.is_power_of_two(), "width must be a power of two");
        debug_assert!(
            8 <= width && width <= 64,
            "width must be in the range [8, 64]"
        );

        Self {
            raw: (width << Self::DATA_SHIFT) | Self::INT,
        }
    }

    int_shorthand!(i8, 8);
    int_shorthand!(i16, 16);
    int_shorthand!(i32, 32);
    int_shorthand!(i64, 64);

    /// Creates a float type (the `fN` types in the IR), with the float being of a given format.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::float(FloatFormat::Double);
    /// let t2 = Type::float(FloatFormat::Single);
    /// assert_ne!(t1, t2);
    /// ```
    pub const fn float(format: FloatFormat) -> Self {
        Self {
            raw: ((format as u32) << Self::DATA_SHIFT) | Self::FLOAT,
        }
    }

    /// Shorthand for `Type::float(FloatFormat::Single)`. Exactly
    /// equivalent to that call.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::f32();
    /// let t2 = Type::float(FloatFormat::Single);
    /// assert_eq!(t1, t2);
    /// ```
    pub const fn f32() -> Self {
        Self::float(FloatFormat::Single)
    }

    /// Shorthand for `Type::float(FloatFormat::Double)`. Exactly
    /// equivalent to that call.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::f64();
    /// let t2 = Type::float(FloatFormat::Double);
    /// assert_eq!(t1, t2);
    /// ```
    pub const fn f64() -> Self {
        Self::float(FloatFormat::Double)
    }

    /// Creates an array type on the given context and returns it.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let ty = Type::array(&mut ctx, Type::i32(), 16); // => [i32; 16]
    /// ```
    pub fn array(ctx: &mut TypeContext, inner: Type, length: usize) -> Self {
        ctx.array(inner, length)
    }

    /// Creates a structure type from a given list of fields.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::new();
    /// let ty = Type::structure(&mut ctx, &[Type::i32(), Type::i32()]); // => { i32, i32 }
    /// ```
    pub fn structure(ctx: &mut TypeContext, fields: &[Type]) -> Self {
        ctx.structure(fields)
    }

    /// Checks if the type is a [`Bool`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_bool(), true);
    /// ```
    pub const fn is_bool(&self) -> bool {
        self.discriminator() == Self::BOOL
    }

    /// Checks if the type is a [`Ptr`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::ptr();
    /// assert_eq!(t1.is_ptr(), true);
    /// ```
    pub const fn is_ptr(&self) -> bool {
        self.discriminator() == Self::PTR
    }

    /// Checks if the type is a [`Int`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::int(32);
    /// assert_eq!(t1.is_int(), true);
    /// ```
    pub const fn is_int(&self) -> bool {
        self.discriminator() == Self::INT
    }

    /// Checks if the type is a [`Int`] and has a given width.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::int(64);
    /// assert_eq!(t1.is_int_of_width(64), true);
    /// ```
    pub const fn is_int_of_width(&self, width: u32) -> bool {
        match (self.discriminator(), self.data()) {
            (Self::INT, w) => w == width,
            _ => false,
        }
    }

    /// Checks if the type is an [`Int`] with a width of 8.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i8();
    /// assert_eq!(t1.is_i8(), true);
    ///
    /// let t2 = Type::f64();
    /// assert_eq!(t2.is_i8(), false);
    /// ```
    #[inline]
    pub const fn is_i8(&self) -> bool {
        self.is_int_of_width(8)
    }

    /// Checks if the type is an [`Int`] with a width of 16.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i16();
    /// assert_eq!(t1.is_i16(), true);
    ///
    /// let t2 = Type::i8();
    /// assert_eq!(t2.is_i16(), false);
    /// ```
    #[inline]
    pub const fn is_i16(&self) -> bool {
        self.is_int_of_width(16)
    }

    /// Checks if the type is an [`Int`] with a width of 32.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i32();
    /// assert_eq!(t1.is_i32(), true);
    ///
    /// let t2 = Type::ptr();
    /// assert_eq!(t2.is_i32(), false);
    /// ```
    #[inline]
    pub const fn is_i32(&self) -> bool {
        self.is_int_of_width(32)
    }

    /// Checks if the type is an [`Int`] with a width of 64.
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::i64().unwrap_int();
    /// assert_eq!(t1.is_i64(), true);
    ///
    /// let t2 = Type::bool();
    /// assert_eq!(t2.is_i64(), false);
    /// ```
    #[inline]
    pub const fn is_i64(&self) -> bool {
        self.is_int_of_width(64)
    }

    /// Checks if the type is a [`Float`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_bool(), true);
    /// ```
    pub const fn is_float(&self) -> bool {
        self.discriminator() == Self::FLOAT
    }

    /// Checks if the type is a [`Float`] and has a given format.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::float(FloatFormat::Double);
    /// assert_eq!(t1.is_float_of_format(FloatFormat::Double), true);
    /// ```
    pub const fn is_float_of_format(&self, format: FloatFormat) -> bool {
        match (self.discriminator(), self.data()) {
            (Self::FLOAT, w) => w == format as u32,
            _ => false,
        }
    }

    /// Checks if the type is a [`Float`] with format [`FloatFormat::Single`].
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::f32();
    /// assert_eq!(t1.is_f32(), true);
    ///
    /// let t2 = Type::i32();
    /// assert_eq!(t2.is_f32(), false);
    /// ```
    #[inline]
    pub const fn is_f32(&self) -> bool {
        self.is_float_of_format(FloatFormat::Single)
    }

    /// Checks if the type is a [`Float`] with format [`FloatFormat::Double`].
    ///
    /// ```
    /// # use sapphire::ir::Type;
    /// let t1 = Type::f64();
    /// assert_eq!(t1.is_f64(), true);
    ///
    /// let t2 = Type::f32();
    /// assert_eq!(t2.is_f64(), false);
    /// ```
    #[inline]
    pub const fn is_f64(&self) -> bool {
        self.is_float_of_format(FloatFormat::Double)
    }

    /// Checks if the type is a [`Array`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_array(), false);
    /// ```
    pub const fn is_array(&self) -> bool {
        self.discriminator() == Self::ARRAY
    }

    /// Checks if the type is a [`Struct`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_struct(), false);
    /// ```
    pub const fn is_struct(&self) -> bool {
        self.discriminator() == Self::STRUCT
    }

    /// If `self` models a boolean type, unwraps the boolean type
    /// and returns it.
    pub fn as_bool(&self) -> Option<Bool> {
        self.is_bool().then_some(Bool(()))
    }

    /// If `self` models a pointer type, unwraps the pointer type
    /// and returns it.
    pub fn as_ptr(&self) -> Option<Ptr> {
        self.is_ptr().then_some(Ptr(()))
    }

    /// If `self` models a integer type, unwraps the integer type
    /// and returns it.
    pub fn as_int(&self) -> Option<Int> {
        self.is_int().then(|| Int::of_width_unchecked(self.data()))
    }

    /// If `self` models a float type, unwraps the float type
    /// and returns it.
    pub fn as_float(&self) -> Option<Float> {
        self.is_float().then(|| {
            Float::new(
                FromPrimitive::from_u32(self.data()).expect("broken data inside of the type"),
            )
        })
    }

    /// If `self` models an array type, unwraps the array type
    /// and returns it.
    pub fn as_array(&self) -> Option<Array> {
        self.is_array().then(|| Array {
            inner: CompoundTypeRef(self.data()),
        })
    }

    /// If `self` models a struct type, unwraps the struct type
    /// and returns it.
    pub fn as_struct(&self) -> Option<Struct> {
        self.is_struct().then(|| Struct {
            inner: CompoundTypeRef(self.data()),
        })
    }

    /// Unpacks a [`Type`] into an [`UType`]. This makes it take up more storage,
    /// but it also means that you can use native `match` and other pattern matching
    /// syntax on the type.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let ty = Type::bool();
    ///
    /// match ty.unpack() {
    ///     UType::Bool(_) => println!("got a bool!"),
    ///     _ => {}
    /// }
    /// ```
    pub fn unpack(self) -> UType {
        match self.discriminator() {
            Self::BOOL => UType::Bool(self.unwrap_bool()),
            Self::PTR => UType::Ptr(self.unwrap_ptr()),
            Self::INT => UType::Int(self.unwrap_int()),
            Self::FLOAT => UType::Float(self.unwrap_float()),
            Self::ARRAY => UType::Array(self.unwrap_array()),
            Self::STRUCT => UType::Struct(self.unwrap_struct()),
            x => unreachable!("invalid discriminant '{}'", x),
        }
    }

    /// Equivalent to [`Self::as_bool`], but panics on failure.
    pub fn unwrap_bool(self) -> Bool {
        self.as_bool()
            .expect("attempted to `Type::unwrap_bool` with wrong internal type")
    }

    /// Equivalent to [`Self::as_ptr`], but panics on failure.
    pub fn unwrap_ptr(self) -> Ptr {
        self.as_ptr()
            .expect("attempted to `Type::unwrap_ptr` with wrong internal type")
    }

    /// Equivalent to [`Self::as_int`], but panics on failure.
    pub fn unwrap_int(self) -> Int {
        self.as_int()
            .expect("attempted to `Type::unwrap_int` with wrong internal type")
    }

    /// Equivalent to [`Self::as_float`], but panics on failure.
    pub fn unwrap_float(self) -> Float {
        self.as_float()
            .expect("attempted to `Type::unwrap_float` with wrong internal type")
    }

    /// Equivalent to [`Self::as_array`], but panics on failure.
    pub fn unwrap_array(self) -> Array {
        self.as_array()
            .expect("attempted to `Type::unwrap_array` with wrong internal type")
    }

    /// Equivalent to [`Self::as_struct`], but panics on failure.
    pub fn unwrap_struct(self) -> Struct {
        self.as_struct()
            .expect("attempted to `Type::unwrap_struct` with wrong internal type")
    }

    fn array_from_ref(ty: CompoundTypeRef) -> Self {
        Self::mask_compound_ref(Self::ARRAY, ty)
    }

    fn struct_from_ref(ty: CompoundTypeRef) -> Self {
        Self::mask_compound_ref(Self::STRUCT, ty)
    }

    fn mask_compound_ref(discriminator: u32, ty: CompoundTypeRef) -> Self {
        Self {
            // ty.0 will not exceed the range of a u29 in a sane program, this would require
            // over 34 gigabytes of (contiguous) data allocated by Vec<CompoundTypeData>
            raw: ty.0 << Self::DATA_SHIFT | discriminator,
        }
    }

    const fn discriminator(&self) -> u32 {
        self.raw & Self::DISCRIMINATOR_MASK
    }

    const fn data(&self) -> u32 {
        (self.raw & Self::DATA_MASK) >> Self::DATA_SHIFT
    }
}

impl From<Type> for UType {
    fn from(value: Type) -> Self {
        value.unpack()
    }
}

impl From<UType> for Type {
    fn from(value: UType) -> Self {
        value.pack()
    }
}

/// An unpacked representation of a [`Type`] that takes up twice as
/// much space, but also has Rust native `enum` semantics.
///
/// When types are being stored, they should be stored as [`Type`]s,
/// but these are fine for computation.
#[repr(u32)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum UType {
    /// A `bool` in the IR.
    Bool(Bool),
    /// A `ptr` in the IR.
    Ptr(Ptr),
    /// An `iN` in the IR.
    Int(Int),
    /// An `fN` in the IR.
    Float(Float),
    /// A `[T; N]` in the IR.
    Array(Array),
    /// A `{ T... }` in the IR.
    Struct(Struct),
}

impl UType {
    /// Re-packs a [`UType`] into a [`Type`]. This is the inverse
    /// of [`Type::unpack`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let ty = Type::ptr();
    /// let unpacked = ty.unpack();
    /// assert_eq!(unpacked.pack(), ty);
    /// ```
    pub fn pack(self) -> Type {
        match self {
            Self::Bool(_) => Type::bool(),
            Self::Ptr(_) => Type::ptr(),
            Self::Int(i) => Type::int(i.width()),
            Self::Float(f) => Type::float(f.format()),
            Self::Array(a) => Type::array_from_ref(a.inner),
            Self::Struct(s) => Type::struct_from_ref(s.inner),
        }
    }
}
