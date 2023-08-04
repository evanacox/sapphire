//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use std::fmt::{Debug, Formatter, Result};
use std::mem;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Helper trait for a type that can be packed into a [`PackedOption`].
///
/// These types need to have some null-ish value that they can reserve,
/// that value will be used to distinguish between `None` and `Some`.
///
/// ```
/// # use sapphire::utility::*;
/// struct NonZero(i32);
///
/// impl Packable for NonZero {
///     fn reserved() -> Self {
///         NonZero(0)
///     }
///
///     fn is_reserved(&self) -> bool {
///         self.0 == 0
///     }
/// }
///
/// let opt = PackedOption::some(NonZero(15));
///
/// assert_eq!(opt.is_some(), true);
/// ```
pub trait Packable {
    /// Gets the reserved value of the type.
    ///
    /// This value is not meant to be constructed normally in any circumstances.
    fn reserved() -> Self;

    /// Checks if the current object is equivalent to the constant
    /// returned by [`Self::reserved`].
    fn is_reserved(&self) -> bool;
}

/// Provides an [`Option`]-like type for [`Packable`] objects without any
/// extra cost to store the flag. It takes up exactly as much space as `T`
/// would on its own, relying on the [`Packable::reserved
///
/// Relies on the null state of a key to distinguish between "none" and "some",
///
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct PackedOption<T: Packable>(T);

impl<T: Packable> PackedOption<T> {
    /// Creates a `None` instance of `PackedOption`.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.is_none(), true);
    /// ```
    #[inline]
    pub fn none() -> Self {
        Self(T::reserved())
    }

    /// Creates a `Some` instance of `PackedOption`.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # struct NonZero(i32);
    /// # impl Packable for NonZero {
    /// #    fn reserved() -> Self {
    /// #        NonZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let opt = PackedOption::some(NonZero(15));
    /// assert_eq!(opt.is_some(), true);
    /// ```
    #[inline]
    pub fn some(value: T) -> Self {
        assert!(!value.is_reserved());

        Self(value)
    }

    /// Returns `true` if the packed option is a `None` value.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.is_none(), true);
    /// ```
    #[inline]
    pub fn is_none(&self) -> bool {
        self.0.is_reserved()
    }

    /// Returns `true` if the packed option is a `Some` value.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct Key; }
    /// let null = PackedOption::<Key>::none();
    /// assert_eq!(null.is_some(), false);
    /// ```
    #[inline]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    /// Expand the packed option into a normal `Option` that can
    /// be pattern-matched on as expected.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct K; }
    /// let null = PackedOption::<K>::none();
    /// assert_eq!(null.expand_ref(), None);
    /// ```
    #[inline]
    pub fn expand_ref(&self) -> Option<&T> {
        if self.is_none() {
            None
        } else {
            Some(&self.0)
        }
    }

    /// Expand the packed option into a normal `Option` that can
    /// be pattern-matched on as expected.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::dense_arena_key;
    /// dense_arena_key! { struct K; }
    /// let null = PackedOption::<K>::none();
    /// assert_eq!(null.expand(), None);
    /// ```
    #[inline]
    pub fn expand(self) -> Option<T> {
        if self.is_none() {
            None
        } else {
            Some(self.0)
        }
    }

    /// Maps a `PackedOption<T>` to `Option<U>` by applying a function to a contained value.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::arena::*;
    /// # use sapphire::dense_arena_key;
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let v = PackedOption::some(NotZero(13));
    /// assert_eq!(v.map(|NotZero(x)| x * 2), Some(26));
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U,
    {
        self.expand().map(f)
    }

    /// Converts a `PackedOption<T>` to `Option<U>` by performing a flatmap operation
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::arena::*;
    /// # use sapphire::dense_arena_key;
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let v = PackedOption::some(NotZero(42));
    /// let f = |NotZero(x)| if x == 42 { None } else { Some(x) };
    /// assert_eq!(v.and_then(f), None);
    /// ```
    #[inline]
    pub fn and_then<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> Option<U>,
    {
        self.expand().and_then(f)
    }

    /// Converts a `PackedOption<T>` to `PackedOption<U>` by performing a flatmap operation
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # use sapphire::arena::*;
    /// # use sapphire::dense_arena_key;
    /// # #[derive(Eq, PartialEq, Debug)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let v = PackedOption::some(NotZero(42));
    /// let f = |NotZero(x)| {
    ///     if x == 42 {
    ///         PackedOption::none()
    ///     } else {
    ///         PackedOption::some(NotZero(x))
    ///     }
    /// };
    ///
    /// assert_eq!(v.and_then_packed(f), None.into());
    /// ```
    #[inline]
    pub fn and_then_packed<U, F>(self, f: F) -> PackedOption<U>
    where
        U: Packable,
        F: FnOnce(T) -> PackedOption<U>,
    {
        if self.is_some() {
            f(self.0)
        } else {
            PackedOption::none()
        }
    }

    /// Unwrap a packed `Some` value or panic.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.unwrap(), NotZero(15));
    /// ```
    #[inline]
    pub fn unwrap(self) -> T {
        if self.is_none() {
            panic!("called `PackedOption::unwrap` on a `None` value");
        }

        self.0
    }

    /// Unwrap a packed `Some` value or panic.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.expect("what?"), NotZero(15));
    /// ```
    #[inline]
    pub fn expect(self, msg: &str) -> T {
        self.expand().expect(msg)
    }

    /// Takes the value out of the packed option, leaving a `None` in its place.
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let mut opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.take(), Some(NotZero(15)));
    /// assert_eq!(opt.is_none(), true);
    /// assert_eq!(opt.take(), None);
    /// ```
    #[inline]
    pub fn take(&mut self) -> Option<T> {
        mem::replace(self, None.into()).expand()
    }

    /// Replaces the value in the packed option, returning the old value (if it existed).
    ///
    /// ```
    /// # use sapphire::utility::*;
    /// # #[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
    /// # struct NotZero(i32);
    /// # impl Packable for NotZero {
    /// #    fn reserved() -> Self {
    /// #        NotZero(0)
    /// #    }    
    /// #    fn is_reserved(&self) -> bool {     
    /// #        self.0 == 0
    /// #     }
    /// # }
    /// let mut opt = PackedOption::some(NotZero(15));
    /// assert_eq!(opt.replace(NotZero(42)), Some(NotZero(15)));
    /// assert_eq!(opt.is_some(), true);
    /// assert_eq!(opt.take(), Some(NotZero(42)));
    /// ```
    #[inline]
    pub fn replace(&mut self, value: T) -> Option<T> {
        mem::replace(self, PackedOption::some(value)).expand()
    }
}

impl<T: Packable> Default for PackedOption<T> {
    fn default() -> Self {
        Self::none()
    }
}

impl<T: Packable> From<Option<T>> for PackedOption<T> {
    fn from(opt: Option<T>) -> Self {
        match opt {
            None => Self::none(),
            Some(t) => Self::some(t),
        }
    }
}

impl<T: Packable> From<PackedOption<T>> for Option<T> {
    fn from(value: PackedOption<T>) -> Self {
        value.expand()
    }
}

impl<T> Debug for PackedOption<T>
where
    T: Packable + Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.expand_ref().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use crate::arena::ArenaMap;
    use crate::dense_arena_key;
    use crate::utility::PackedOption;

    dense_arena_key! {
        struct E;
    }

    #[test]
    fn observer_methods() {
        let mut map = ArenaMap::default();
        let key: E = map.insert("Hello!");

        let none = PackedOption::default();
        let mut some = PackedOption::some(key);

        assert!(none.is_none());
        assert!(!none.is_some());
        assert!(!some.is_none());
        assert!(some.is_some());

        some = none;

        assert!(some.is_none());
        assert!(!some.is_some());
    }
}
