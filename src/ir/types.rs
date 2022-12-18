//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use ahash::AHashMap;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use static_assertions::assert_eq_size;
use std::hash::Hash;

// this is the type stored inside of `Type`, it's packed so that the whole
// type ends up being 16 bytes.
#[repr(packed)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct PackedCompoundTypeRef(u64, u32);

// this is what's actually passed around everywhere, it's not packed for alignment reasons
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct CompoundTypeRef(u64, u32);

impl Into<PackedCompoundTypeRef> for CompoundTypeRef {
    fn into(self) -> PackedCompoundTypeRef {
        PackedCompoundTypeRef(self.0, self.1)
    }
}

impl Into<CompoundTypeRef> for PackedCompoundTypeRef {
    fn into(self) -> CompoundTypeRef {
        CompoundTypeRef(self.0, self.1)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
enum CompoundTypeData {
    Array(Type, u32),
    Struct(SmallVec<[Type; 2]>),
}

impl CompoundTypeData {
    fn as_array(&self) -> Option<(Type, u32)> {
        match self {
            CompoundTypeData::Array(ty, len) => Some((*ty, *len)),
            _ => None,
        }
    }

    fn as_struct(&self) -> Option<&[Type]> {
        match self {
            CompoundTypeData::Struct(tys) => Some(tys),
            _ => None,
        }
    }
}

/// Owns the actual data for all of the compound types in a given module. Types are
/// de-duplicated on creation, to ensure that equality based on their "key" is equivalent
/// to comparison by value.
///
/// # Implementation
/// The underlying structure is a hash table mapping the hash of the compound type
/// to a list of compound types with that hash, where the "key" is both the hash of
/// the type (to lookup inside the map) and the index into that array.
///
/// This guarantees that hash collisions don't break everything (however unlikely
/// they are, given the full `u64` hash value is being used), while also still
/// allowing unique-ness to be determined trivially when a type with the same hash code
/// doesn't already exist.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct TypeContext {
    lookup: AHashMap<u64, SmallVec<[CompoundTypeData; 1]>>,
}

impl TypeContext {
    /// Creates an empty context that is ready for use in a module.
    pub fn new() -> Self {
        Self {
            lookup: AHashMap::default(),
        }
    }

    fn create_array(&mut self, inner: Type, length: u32) -> CompoundTypeRef {
        let data = CompoundTypeData::Array(inner, length);
        let mut hasher = WyHash::default();

        inner.hash(&mut hasher);
        length.hash(&mut hasher);

        self.insert(data, hasher.finish())
    }

    fn create_struct(&mut self, elements: &[Type]) -> CompoundTypeRef {
        let data = CompoundTypeData::Struct(elements.into());
        let mut hasher = WyHash::default();

        elements.hash(&mut hasher);

        self.insert(data, hasher.finish())
    }

    fn insert(&mut self, data: CompoundTypeData, hash: u64) -> CompoundTypeRef {
        // if the key isn't in the map, insert an empty SmallVec at the key.
        // either way, get the vec at the key (newly inserted or not).
        let vec = self.lookup.entry(hash).or_default();

        // if `data` is inside of that vec, return a key that maps to the index of it.
        // if it doesn't, push it to the end and return a key with that new index
        match vec.iter().position(&data) {
            Some(n) => CompoundTypeRef(hash, n as u32),
            None => {
                vec.push(data);

                CompoundTypeRef(hash, (vec.len() - 1) as u32)
            }
        }
    }

    fn info_for(&self, ty_ref: CompoundTypeRef) -> &CompoundTypeData {
        &self.lookup[ty_ref.0][ty_ref.1]
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
/// let t1 = Int::i8();
/// assert_eq!(t1.width(), 8);
/// assert_eq!(t1.mask(), 0xFF);
/// assert_eq!(t1.sign_bit(), 0b1000_0000);
///
/// let t2 = Int::new(8);
/// assert_eq!(t1, t2);
///
/// let t3 = Int::i64();
/// assert_ne!(t1, t3);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Int {
    width: u32,
}

macro_rules! int_const_shorthand {
    ($n:tt, $lower:ident) => {
        #[doc = concat!("Shorthand for creating an integer of width `", stringify!($n), "`.")]
        #[doc = concat!("Exactly equivalent to `IntType::new(", stringify!($n), ")`.")]
        #[doc = ""]
        #[doc = "# Example"]
        #[doc = "```"]
        #[doc = "# use sapphire::ir::IntType;"]
        #[doc = concat!("let t1 = IntType::i", stringify!($n), "();")]
        #[doc = concat!("let t2 = IntType::new(", stringify!($n), ");")]
        #[doc = ""]
        #[doc = "assert_eq!(t1, t2);"]
        #[doc = "```"]
        pub const fn $lower() -> Self {
            Self::of_width_unchecked($n)
        }
    };
}

impl Int {
    #[inline]
    const fn of_width_unchecked(bit_width: u32) -> Self {
        Self { width: bit_width }
    }

    /// Creates an `Int` with a given width.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let ty = Int::new(32); // ty => i32
    ///
    /// assert_eq!(ty.width(), 32);
    /// ```
    #[inline]
    pub fn new(bit_width: u32) -> Option<Self> {
        match bit_width {
            8 => Some(Self::i8()),
            16 => Some(Self::i16()),
            32 => Some(Self::i32()),
            64 => Some(Self::i64()),
            _ => None,
        }
    }

    int_const_shorthand!(8, i8);
    int_const_shorthand!(16, i16);
    int_const_shorthand!(32, i32);
    int_const_shorthand!(64, i64);

    /// Gets the width of the integer.
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let ty = Int::new(64);
    ///
    /// assert_eq!(ty.width(), 64);
    /// ```
    #[inline]
    pub fn width(self) -> u64 {
        self.width as u64
    }

    /// Returns a mask with the sign bit (MSB in 2's complement) set for
    /// an integer of `self.width()` width.
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let t1 = Int::i32();
    /// let t2 = Int::i8();
    ///
    /// assert_eq!(t1.sign_bit(), 0x80000000);
    /// assert_eq!(t2.sign_bit(), 0b1000_0000);
    /// ```
    #[inline]
    pub fn sign_bit(self) -> u64 {
        1u64 << ((self.width() as u64) - 1)
    }

    /// Returns a mask with every usable bit in the type set. This equivalent
    /// to the value resulting from the instruction `xor iN $x, -1`
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let t1 = Int::new(64);
    /// let t2 = Int::new(16);
    ///
    /// assert_eq!(t1.mask(), 0xFFFFFFFFFFFFFFFF);
    /// assert_eq!(t2.mask(), 0b1111_1111_1111_1111);
    /// ```
    #[inline]
    pub fn mask(self) -> u64 {
        !0u64 >> (64 - self.width())
    }

    /// Checks if the integer type has a width of 8.
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let t1 = Int::new(8);
    /// assert_eq!(t1.is_i8(), true);
    ///
    /// let t2 = Int::new(32);
    /// assert_eq!(t2.is_i8(), false);
    /// ```
    #[inline]
    pub const fn is_i8(self) -> bool {
        self.width == 8
    }

    /// Checks if the integer type has a width of 16.
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let t1 = Int::new(16);
    /// assert_eq!(t1.is_i16(), true);
    ///
    /// let t2 = Int::new(64);
    /// assert_eq!(t2.is_i16(), false);
    /// ```
    #[inline]
    pub const fn is_i16(self) -> bool {
        self.width == 16
    }

    /// Checks if the integer type has a width of 32.
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let t1 = Int::new(32);
    /// assert_eq!(t1.is_i32(), true);
    ///
    /// let t2 = Int::new(16);
    /// assert_eq!(t2.is_i32(), false);
    /// ```
    #[inline]
    pub const fn is_i32(self) -> bool {
        self.width == 32
    }

    /// Checks if the integer type has a width of 64.
    ///
    /// ```
    /// # use sapphire::ir::Int;
    /// let t1 = Int::new(64);
    /// assert_eq!(t1.is_i64(), true);
    ///
    /// let t2 = Int::new(8);
    /// assert_eq!(t2.is_i64(), false);
    /// ```
    #[inline]
    pub const fn is_i64(self) -> bool {
        self.width == 64
    }
}

/// Maps the hardware representation of the floating-point types
/// to enum variants.
///
/// These map directly to types defined in the IEEE-754 standard.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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
/// See `fN` in the [Reference](https://pages.evanacox.io/quartz/qir/reference#fn-floats).
///
/// ```
/// # use sapphire::ir::*;
/// let t1 = Type::float(FloatFormat::Single);
/// let t2 = Type::f32();
///
/// assert_eq!(t1, t2);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Float {
    real: FloatFormat,
}

impl Float {
    /// Creates an `fN` type from a given IEEE floating-point type
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Float::new(FloatFormat::Single);
    /// let t2 = Float::f32();
    ///
    /// assert_eq!(t1, t2);
    /// ```
    #[inline]
    pub const fn new(real: FloatFormat) -> Self {
        Self { real }
    }

    /// Creates an `f32` type
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Float::new(FloatFormat::Single);
    /// let t2 = Float::f32();
    ///
    /// assert_eq!(t1, t2);
    /// ```
    #[inline]
    pub const fn f32() -> Self {
        Self::new(FloatFormat::Single)
    }

    /// Creates an `f64` type
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Float::new(FloatFormat::Double);
    /// let t2 = Float::f64();
    ///
    /// assert_eq!(t1, t2);
    /// ```
    #[inline]
    pub const fn f64() -> Self {
        Self::new(FloatFormat::Double)
    }

    /// Gets the underlying IEEE floating-point type from a given `fN` type
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Float::new(FloatFormat::Single);
    ///
    /// assert_eq!(t1.format(), FloatFormat::Single);
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
    inner: PackedCompoundTypeRef,
}

impl Array {
    pub fn len(&self, ctx: &TypeContext) -> u32 {
        self.data(ctx).1
    }

    pub fn is_empty(&self, ctx: &TypeContext) -> bool {
        self.len(ctx) == 0
    }

    pub fn element(&self, ctx: &TypeContext) -> Type {
        self.data(ctx).0
    }

    fn data(&self, ctx: &TypeContext) -> (Type, u32) {
        ctx.info_for(self.inner.into())
            .as_array()
            .expect("somehow got `Type::Array` that refers to non-array type")
    }
}

/// Models a structure type in the IR. Internally, contains a reference into
/// the [`TypeContext`] that is being used for the module being operated on.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Struct {
    inner: PackedCompoundTypeRef,
}

impl Struct {
    pub fn members(&self, ctx: &TypeContext) -> &[Type] {
        ctx.info_for(self.inner.into())
            .as_struct()
            .expect("somehow got `Type::Struct` that refers to non-struct type")
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
#[repr(u32)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum Type {
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

// the types should be exactly 2 words on modern systems. we abuse `#[repr(packed)]`
// with the `CompoundTypeRef` to make sure that the discriminant of `Type` can be stored in
// the 4 bytes that would otherwise be used as padding.
assert_eq_size!(Type, (usize, usize));

impl Type {
    /// Creates a boolean type (the `bool` type in the IR).
    pub fn bool() -> Self {
        Self::Bool(Bool(()))
    }

    /// Creates a pointer type (the `ptr` type in the IR).
    pub fn ptr() -> Self {
        Self::Ptr(Ptr(()))
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
    pub fn int(width: u32) -> Self {
        debug_assert!(width.is_power_of_two(), "width must be a power of two");
        debug_assert!(
            8 <= width && width <= 64,
            "width must be in the range [8, 64]"
        );

        Self::Int(Int { width })
    }

    /// Creates a float type (the `fN` types in the IR), with the float being of a given format.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::float(FloatFormat::IEEEDouble);
    /// let t2 = Type::float(FloatFormat::IEEESingle);
    /// assert_ne!(t1, t2);
    /// ```
    pub fn float(format: FloatFormat) -> Self {
        Self::Float(Float { real: format })
    }

    /// Creates an array type (the `[T; N]` types in the IR). Note that these
    /// need to be stored inside of a context.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::default();
    /// let t1 = Type::array(&mut ctx, Type::bool(), 512);
    /// let t2 = Type::array(&mut ctx, Type::ptr(), 16);
    /// assert_ne!(t1, t2);
    /// ```
    pub fn array(ctx: &mut TypeContext, inner: Type, length: u32) -> Self {
        Self::Array(Array {
            inner: ctx.create_array(inner, length).into(),
        })
    }

    /// Creates a struct type (the `{ T... }` types in the IR). Note that these
    /// need to be stored inside of a context.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let mut ctx = TypeContext::default();
    /// let t1 = Type::structure(&mut ctx, &[]); // {}
    /// let t2 = Type::structure(&mut ctx, &[Type::ptr(), Type::int(64)]); // { ptr, i64 }
    /// assert_ne!(t1, t2);
    /// ```
    pub fn structure(ctx: &mut TypeContext, tys: &[Type]) -> Self {
        Self::Struct(Struct {
            inner: ctx.create_struct(tys).into(),
        })
    }

    /// Checks if the type is a [`Bool`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_bool(), true);
    /// ```
    pub fn is_bool(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            _ => false,
        }
    }

    /// Checks if the type is a [`Ptr`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::ptr();
    /// assert_eq!(t1.is_ptr(), true);
    /// ```
    pub fn is_ptr(&self) -> bool {
        match self {
            Self::Ptr(_) => true,
            _ => false,
        }
    }

    /// Checks if the type is a [`Int`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::int(32);
    /// assert_eq!(t1.is_int(), true);
    /// ```
    pub fn is_int(&self) -> bool {
        match self {
            Self::Int(_) => true,
            _ => false,
        }
    }

    /// Checks if the type is a [`Int`] and has a given width.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::int(64);
    /// assert_eq!(t1.is_int_of_width(64), true);
    /// ```
    pub fn is_int_of_width(&self, width: u32) -> bool {
        match self {
            Self::Int(i) => i.bits() == width,
            _ => false,
        }
    }

    /// Checks if the type is a [`Float`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_bool(), true);
    /// ```
    pub fn is_float(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            _ => false,
        }
    }

    /// Checks if the type is a [`Float`] and has a given format.
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::float(FloatFormat::Double);
    /// assert_eq!(t1.is_float_of_format(FloatFormat::Double), true);
    /// ```
    pub fn is_float_of_format(&self, format: FloatFormat) -> bool {
        match self {
            Self::Float(f) => f.format() == format,
            _ => false,
        }
    }

    /// Checks if the type is a [`Array`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_array(), false);
    /// ```
    pub fn is_array(&self) -> bool {
        match self {
            Self::Array(_) => true,
            _ => false,
        }
    }

    /// Checks if the type is a [`Struct`].
    ///
    /// ```
    /// # use sapphire::ir::*;
    /// let t1 = Type::bool();
    /// assert_eq!(t1.is_struct(), false);
    /// ```
    pub fn is_struct(&self) -> bool {
        match self {
            Self::Struct(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_int(self) -> Int {
        match self {
            Self::Int(i) => i,
            _ => panic!(
                "attempted to read `Type::unwrap_int` with type '{:?}'",
                self
            ),
        }
    }

    pub fn unwrap_float(self) -> Float {
        match self {
            Self::Float(f) => f,
            _ => panic!(
                "attempted to read `Type::unwrap_float` with type '{:?}'",
                self
            ),
        }
    }

    pub fn unwrap_array(self) -> Array {
        match self {
            Self::Array(a) => a,
            _ => panic!(
                "attempted to read `Type::unwrap_array` with type '{:?}'",
                self
            ),
        }
    }

    pub fn unwrap_struct(self) -> Struct {
        match self {
            Self::Struct(s) => s,
            _ => panic!(
                "attempted to read `Type::unwrap_struct` with type '{:?}'",
                self
            ),
        }
    }
}
