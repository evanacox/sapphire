//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use smallvec::SmallVec;
use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};
use std::{fmt, mem, ptr, slice};

#[cfg(feature = "enable-serde")]
use serde::{
    de::{SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

union Storage<T, const N: usize> {
    inline: ManuallyDrop<[T; N]>,
    heap: *mut T,
}

/// A tiny, specialized container for one purpose: storing immutable
/// arrays into data structures that need to be compact. This is effectively
/// a small-size optimized [`Box<[T]>`].
///
/// This is meant to be constructed from a [`Vec<T>`] or similar once the
/// size is known to no longer need to change. Then the heap allocation will
/// either be taken from the [`Vec`] or deallocated entirely.
///
/// Ideally, this type is used so that `sizeof([T; N]) == sizeof(usize)`, which
/// makes this type be exactly pointer-sized.
///
/// ```
/// # use sapphire::utility::TinyArray;
/// let vec = vec![1, 2, 3, 4]; // ideally more complicated logic
/// let tiny = TinyArray::<i16, 4>::from_vec(vec);
///
/// assert_eq!(tiny.as_slice(), &[1, 2, 3, 4]);
/// ```
///
/// [`TinyArray`]s still work like normal arrays as expected.
///
/// ```
/// # use sapphire::utility::TinyArray;
/// let tiny = TinyArray::<i32, 2>::from_vec(vec![1, 2]);
///
/// assert_eq!(tiny[0], 1);
/// assert_eq!(tiny[1], 2);
/// ```
pub struct TinyArray<T, const N: usize> {
    len: usize,
    data: Storage<T, N>,
}

impl<T, const N: usize> TinyArray<T, N> {
    fn from_large_buffer(mut vec: Vec<T>) -> Self {
        vec.shrink_to_fit();

        Self::from_raw_parts(vec.into_raw_parts())
    }

    fn from_inline_buffer(buffer: [T; N]) -> Self {
        Self {
            len: N,
            data: Storage {
                inline: ManuallyDrop::new(buffer),
            },
        }
    }

    fn from_small_buffer(mut vec: SmallVec<[T; N]>) -> Self
    where
        [T; N]: smallvec::Array<Item = T>,
    {
        vec.shrink_to_fit();

        // this will not allocate, we know that `vec` has already spilled onto the heap
        Self::from_raw_parts(vec.into_vec().into_raw_parts())
    }

    fn from_raw_parts((ptr, len, _): (*mut T, usize, usize)) -> Self {
        Self {
            len,
            data: Storage { heap: ptr },
        }
    }

    /// Creates a [`TinyArray`] from a given [`Vec`].
    ///
    /// If the vec fits inside the tiny inline array, the heap allocation will be deallocated.
    pub fn from_vec(vec: Vec<T>) -> Self {
        match <[T; N] as TryFrom<Vec<T>>>::try_from(vec) {
            Ok(array) => Self::from_inline_buffer(array),
            Err(vec) => Self::from_large_buffer(vec),
        }
    }

    /// Creates a [`TinyArray<T, N>`] from a given `SmallVec<[T; N]>`.
    ///
    /// If the vec fits inside the tiny inline array, it will be put there instead.
    pub fn from_small_vec(vec: SmallVec<[T; N]>) -> Self {
        match vec.into_inner() {
            Ok(inner) => Self::from_inline_buffer(inner),
            Err(vec) => Self::from_small_buffer(vec),
        }
    }

    /// Creates an inline [`TinyArray`] from an array
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let arr = TinyArray::from_arr([1, 2, 3, 4, 5]);
    /// assert_eq!(arr.as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    pub fn from_arr(array: [T; N]) -> Self {
        Self::from_inline_buffer(array)
    }

    /// Creates a [`TinyArray`] by cloning elements from a slice.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2, 3];
    /// let arr = TinyArray::<i32, 2>::from_slice(&v);
    /// assert_eq!(arr.as_slice(), &[1, 2, 3]);
    /// ```
    pub fn from_slice<'a>(slice: &'a [T]) -> Self
    where
        T: Clone,
    {
        match <&'a [T; N] as TryFrom<&'a [T]>>::try_from(slice) {
            Ok(array) => Self::from_inline_buffer(array.clone()),
            Err(_) => Self::from_large_buffer(slice.to_vec()),
        }
    }

    /// Checks if `self` is in the inline state.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2];
    /// let inline = TinyArray::<i32, 2>::from_vec(v);
    /// assert_eq!(inline.is_inline(), true);
    /// ```
    pub fn is_inline(&self) -> bool {
        self.len == N
    }

    /// Checks if `self` is in the heap-allocated state.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2, 3, 4, 5];
    /// let heap = TinyArray::<i32, 1>::from_vec(v);
    /// assert_eq!(heap.is_spilled(), true);
    /// ```
    pub fn is_spilled(&self) -> bool {
        !self.is_inline()
    }

    /// Returns the length of the array.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2, 3, 4, 5];
    /// let heap = TinyArray::<i32, 1>::from_vec(v);
    /// assert_eq!(heap.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Checks if the array is empty.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2];
    /// let heap = TinyArray::<i32, 2>::from_vec(v);
    /// assert_eq!(heap.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Gets the underlying array as a slice.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2];
    /// let arr = TinyArray::<i32, 2>::from_vec(v);
    /// assert_eq!(arr.as_slice(), &[1, 2]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.data(), self.len) }
    }

    /// Gets the underlying array as a slice.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2];
    /// let mut arr = TinyArray::<i32, 2>::from_vec(v);
    /// assert_eq!(arr.as_slice_mut(), &mut [1, 2]);
    /// ```
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.data_mut(), self.len) }
    }

    /// Gets the underlying array as a slice.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2];
    /// let arr = TinyArray::<i32, 2>::from_vec(v);
    /// let mut it = arr.iter();
    /// assert_eq!(it.next(), Some(&1));
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.as_slice().iter()
    }

    /// Gets the underlying array as a slice.
    ///
    /// ```
    /// # use sapphire::utility::TinyArray;
    /// let v = vec![1, 2];
    /// let mut arr = TinyArray::<i32, 2>::from_vec(v);
    /// let mut it = arr.iter_mut();
    /// assert_eq!(it.next(), Some(&mut 1));
    /// ```
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.as_slice_mut().iter_mut()
    }

    fn data(&self) -> *const T {
        unsafe {
            if self.is_inline() {
                (*self.inline_ptr()).as_ptr()
            } else {
                self.spilled_ptr()
            }
        }
    }

    fn data_mut(&mut self) -> *mut T {
        unsafe {
            if self.is_inline() {
                (*self.inline_ptr_mut()).as_mut_ptr()
            } else {
                self.spilled_ptr_mut()
            }
        }
    }

    unsafe fn inline_ptr(&self) -> *const [T; N] {
        debug_assert!(self.is_inline());

        (&*self.data.inline) as *const _
    }

    unsafe fn inline_ptr_mut(&mut self) -> *mut [T; N] {
        debug_assert!(self.is_inline());

        (&mut *self.data.inline) as *mut _
    }

    unsafe fn inline_array(&self) -> &[T; N] {
        debug_assert!(self.is_inline());

        &self.data.inline
    }

    unsafe fn inline_array_mut(&mut self) -> &mut [T; N] {
        debug_assert!(self.is_inline());

        &mut self.data.inline
    }

    unsafe fn spilled_ptr(&self) -> *const T {
        debug_assert!(self.is_spilled());

        self.data.heap
    }

    unsafe fn spilled_ptr_mut(&mut self) -> *mut T {
        debug_assert!(self.is_spilled());

        self.data.heap
    }

    unsafe fn spilled(&self) -> &[T] {
        debug_assert!(self.is_spilled());

        slice::from_raw_parts(self.data.heap, self.len)
    }

    unsafe fn spilled_mut(&mut self) -> &mut [T] {
        debug_assert!(self.is_spilled());

        slice::from_raw_parts_mut(self.data.heap, self.len)
    }
}

impl<T, const N: usize> Deref for TinyArray<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> Borrow<[T]> for TinyArray<T, N> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> BorrowMut<[T]> for TinyArray<T, N> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T, const N: usize> DerefMut for TinyArray<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}

#[derive(Debug)]
enum TinyArrayIntoIter<T, const N: usize> {
    Inline(std::array::IntoIter<T, N>),
    Heap(std::vec::IntoIter<T>),
}

/// Implements IntoIter for a [`TinyArray`].
///
/// Values are yielded regardless of their location in memory, and the underlying
/// array is freed once the iterator is dropped.
#[derive(Debug)]
pub struct IntoIter<T, const N: usize> {
    data: TinyArrayIntoIter<T, N>,
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.data {
            TinyArrayIntoIter::Inline(i) => i.next(),
            TinyArrayIntoIter::Heap(i) => i.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.data {
            TinyArrayIntoIter::Inline(i) => i.size_hint(),
            TinyArrayIntoIter::Heap(i) => i.size_hint(),
        }
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match &mut self.data {
            TinyArrayIntoIter::Inline(i) => i.next_back(),
            TinyArrayIntoIter::Heap(i) => i.next_back(),
        }
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N> {}

impl<T, const N: usize> IntoIterator for TinyArray<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(mut self) -> Self::IntoIter {
        let data = unsafe {
            if self.is_inline() {
                let buf = ptr::read(&*self.data.inline);

                TinyArrayIntoIter::Inline(buf.into_iter())
            } else {
                let vec = Vec::from_raw_parts(self.spilled_ptr_mut(), self.len, self.len);

                TinyArrayIntoIter::Heap(vec.into_iter())
            }
        };

        // we don't need to drop anything, the IntoIter will take care of it
        mem::forget(self);

        Self::IntoIter { data }
    }
}

impl<T, const N: usize> Debug for TinyArray<T, N>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, const N: usize> Clone for TinyArray<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        if self.is_spilled() {
            // we need to duplicate our allocation anyway, may as well just let `Vec`
            // do it for us instead of re-inventing the wheel
            let vec = Vec::from_iter(self.iter().cloned());

            Self::from_large_buffer(vec)
        } else {
            // in the inline case, we don't want to allocate temporarily so we directly
            // clone the underlying array from `self`
            Self {
                len: self.len,
                data: Storage {
                    inline: unsafe { ManuallyDrop::new((*self.inline_ptr()).clone()) },
                },
            }
        }
    }
}

impl<T, U, const N: usize, const M: usize> PartialEq<TinyArray<U, M>> for TinyArray<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &TinyArray<U, M>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}

impl<T, const N: usize> Eq for TinyArray<T, N> where T: Eq {}

impl<T, const N: usize, const M: usize> PartialOrd<TinyArray<T, M>> for TinyArray<T, N>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &TinyArray<T, M>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T, const N: usize> Ord for TinyArray<T, N>
where
    T: Ord,
{
    fn cmp(&self, other: &TinyArray<T, N>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T, const N: usize> Hash for TinyArray<T, N>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state)
    }
}

impl<T, const N: usize> FromIterator<T> for TinyArray<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Self {
        match it.into_iter().collect::<SmallVec<[T; N]>>().into_inner() {
            Ok(array) => Self::from_inline_buffer(array),
            Err(vec) => Self::from_small_buffer(vec),
        }
    }
}

impl<T, const N: usize> Drop for TinyArray<T, N> {
    fn drop(&mut self) {
        unsafe {
            // if we have spilled, we need to let vec do all the dropping since we don't know
            // exactly how the vector allocated the memory and thus can't deallocate it
            if self.is_spilled() {
                drop(Vec::from_raw_parts(
                    self.spilled_ptr_mut(),
                    self.len,
                    self.len,
                ));
            } else {
                // if we haven't spilled, we can just drop all the elements and let the union's drop
                // handle the space taken up by the array. not our problem
                ptr::drop_in_place(slice::from_raw_parts_mut(
                    (*self.inline_ptr_mut()).as_mut_ptr(),
                    self.len,
                ));
            }
        }
    }
}

#[cfg(feature = "enable-serde")]
impl<T, const N: usize> Serialize for TinyArray<T, N>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_seq(self.iter())
    }
}

#[cfg(feature = "enable-serde")]
struct TinyArrayVisitor<'de, T, const N: usize>(PhantomData<fn() -> [&'de T; N]>)
where
    T: Deserialize<'de>;

#[cfg(feature = "enable-serde")]
impl<'de, T, const N: usize> Visitor<'de> for TinyArrayVisitor<'de, T, N>
where
    T: Deserialize<'de>,
{
    type Value = TinyArray<T, N>;

    fn expecting(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(formatter, "a sequence of `str` values")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let size = seq.size_hint().unwrap_or(128);
        let mut values = Vec::with_capacity(size);

        while let Some(value) = seq.next_element()? {
            values.push(value);
        }

        Ok(TinyArray::from_vec(values))
    }
}

#[cfg(feature = "enable-serde")]
impl<'de, T, const N: usize> Deserialize<'de> for TinyArray<T, N>
where
    T: Deserialize<'de> + 'de,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(TinyArrayVisitor(PhantomData::default()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;
    use std::cell::RefCell;
    use std::collections::VecDeque;

    #[test]
    fn from_vec() {
        let arr = TinyArray::<i32, 2>::from_vec(vec![1, 2, 3]);

        assert!(arr.is_spilled());
        assert_eq!(arr[0], 1);
        assert_eq!(arr[1], 2);
        assert_eq!(arr[2], 3);
    }

    #[test]
    fn from_small_vec() {
        let small = smallvec![1, 2, 3, 4];
        let arr = TinyArray::<i16, 4>::from_small_vec(small);

        assert!(arr.is_inline());
        assert_eq!(arr.len(), 4);
        assert_eq!(arr[0], 1);
        assert_eq!(arr[1], 2);
        assert_eq!(arr[2], 3);
        assert_eq!(arr[3], 4);
    }

    #[test]
    fn from_iter() {
        let deque = VecDeque::from([1, 2, 3, 4]);
        let arr = TinyArray::<i16, 4>::from_iter(deque.into_iter());

        assert!(arr.is_inline());
        assert_eq!(arr.len(), 4);
        assert_eq!(arr[0], 1);
        assert_eq!(arr[1], 2);
        assert_eq!(arr[2], 3);
        assert_eq!(arr[3], 4);
    }

    #[test]
    fn from_array() {
        let arr = TinyArray::from_arr([1, 2, 3]);

        assert!(arr.is_inline());
        assert_eq!(arr.len(), 3);
        assert_eq!(arr[0], 1);
        assert_eq!(arr[1], 2);
        assert_eq!(arr[2], 3);
    }

    #[test]
    fn iter() {
        let arr = TinyArray::<i32, 2>::from_vec(vec![1, 2, 3, 4]);

        for (i, val) in arr.iter().enumerate() {
            assert_eq!(i + 1, *val as usize);
        }
    }

    #[test]
    fn iter_mut() {
        let mut arr = TinyArray::<i32, 2>::from_vec(vec![1, 2, 3, 4]);

        for (i, val) in arr.iter_mut().enumerate() {
            assert_eq!(i + 1, *val as usize);
        }
    }

    #[test]
    fn into_iter() {
        let arr = TinyArray::<i32, 2>::from_vec(vec![1, 2, 3, 4]);

        for (i, val) in arr.into_iter().enumerate() {
            assert_eq!(i + 1, val as usize);
        }
    }

    #[test]
    fn eq() {
        // inline
        {
            let a1 = TinyArray::from_arr([1, 2]);
            let a2 = TinyArray::from_arr([1, 2]);
            let a3 = TinyArray::from_arr([3, 4]);
            let a4 = TinyArray::from_arr([1, 2, 3]);

            assert_eq!(a1, a2);
            assert_ne!(a1, a3);
            assert_ne!(a1, a4);
        }

        // spilled
        {
            let a1 = TinyArray::<i32, 1>::from_vec(vec![1, 2]);
            let a2 = TinyArray::<i32, 1>::from_vec(vec![1, 2]);
            let a3 = TinyArray::<i32, 1>::from_vec(vec![3, 4]);
            let a4 = TinyArray::<i32, 1>::from_vec(vec![1, 2, 3]);

            assert_eq!(a1, a2);
            assert_ne!(a1, a3);
            assert_ne!(a1, a4);
        }

        // mixed inline/spilled
        {
            let a1 = TinyArray::<i32, 1>::from_vec(vec![1, 2]);
            let a2 = TinyArray::from_arr([1, 2]);
            let a3 = TinyArray::<i32, 1>::from_vec(vec![1, 2, 3]);
            let a4 = TinyArray::from_arr([1, 2, 3]);

            assert_eq!(a1, a2);
            assert_eq!(a3, a4);
            assert_ne!(a1, a3);
            assert_ne!(a2, a4);
        }

        // mixed types
        {
            let a1 = TinyArray::from_arr([1, 2]);
            let a2 = TinyArray::from_arr([1i16, 2i16]);

            assert_eq!(a1, a2);
        }
    }

    #[test]
    fn clone() {
        // inline
        {
            let arr1 = TinyArray::<i32, 2>::from_arr([1, 2]);
            let arr2 = arr1.clone();

            assert_eq!(arr1, arr2);
        }

        // heap
        {
            let a1 = TinyArray::<i32, 1>::from_vec(vec![1, 2]);
            let a2 = a1.clone();

            assert_eq!(a1, a2);
        }
    }

    struct CountsDrops<'a>(&'a RefCell<usize>);

    impl<'a> Drop for CountsDrops<'a> {
        fn drop(&mut self) {
            *self.0.borrow_mut() += 1;
        }
    }

    #[test]
    fn drop() {
        let counter = RefCell::new(0usize);

        // inline
        {
            let _ = TinyArray::from_arr([CountsDrops(&counter), CountsDrops(&counter)]);
        }

        assert_eq!(*counter.borrow(), 2);

        *counter.borrow_mut() = 0;

        // spilled
        {
            let _ = TinyArray::<CountsDrops<'_>, 1>::from_vec(vec![
                CountsDrops(&counter),
                CountsDrops(&counter),
            ]);
        }

        assert_eq!(*counter.borrow(), 2);
    }

    #[test]
    fn into_iter_drop() {
        let counter = RefCell::new(0usize);

        // inline
        {
            let arr = TinyArray::from_arr([CountsDrops(&counter), CountsDrops(&counter)]);

            for _ in arr.into_iter() {}
        }

        assert_eq!(*counter.borrow(), 2);

        *counter.borrow_mut() = 0;

        // spilled
        {
            let arr = TinyArray::<CountsDrops<'_>, 1>::from_vec(vec![
                CountsDrops(&counter),
                CountsDrops(&counter),
            ]);

            for _ in arr.into_iter() {}
        }

        assert_eq!(*counter.borrow(), 2);
    }

    #[test]
    fn from_slice() {
        // inline
        {
            let v = vec![1, 2, 3, 4];
            let a = [1, 2, 3, 4];

            let t1 = TinyArray::<i32, 4>::from_slice(&v);
            let t2 = TinyArray::<i32, 4>::from_slice(&a);

            assert_eq!(v, a);
            assert!(t1.is_inline());
            assert!(t2.is_inline());
        }

        // spilled
        {
            let v = vec![1, 2, 3, 4, 5];
            let a = [1, 2, 3, 4, 5];

            let t1 = TinyArray::<i32, 2>::from_slice(&v);
            let t2 = TinyArray::<i32, 2>::from_slice(&a);

            assert_eq!(v, a);
            assert!(t1.is_spilled());
            assert!(t2.is_spilled());
        }
    }

    #[cfg(feature = "enable-serde")]
    use serde_test::{assert_tokens, Token};

    #[test]
    #[cfg(feature = "enable-serde")]
    fn serialize() {
        fn matches<const N: usize>(arr: &TinyArray<i32, N>) {
            assert_tokens(
                arr,
                &[
                    Token::Seq { len: Some(4) },
                    Token::I32(1),
                    Token::I32(2),
                    Token::I32(3),
                    Token::I32(4),
                    Token::SeqEnd,
                ],
            );
        }

        // inline
        {
            matches(&TinyArray::from_arr([1, 2, 3, 4]));
        }

        // spilled
        {
            matches(&TinyArray::<i32, 1>::from_vec(vec![1, 2, 3, 4]));
        }
    }
}
