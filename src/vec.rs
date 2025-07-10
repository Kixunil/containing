//! Provides a specialized implementaion of `NonEmpty<Vec<T>>`
//!
//! Because it is currenly not possible to explain to the compiler that the length and capacity
//! inside `NonEmpty<Vec<T>>` are never zero this module provides a separate type that can do that.
//! It's recommended to use it in enums variants and structs that might go into enum variants to
//! give the compiler a chance to optimize the layout.

use alloc::vec::Vec;
use alloc::collections::TryReserveError;
use core::fmt;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroUsize;
use core::ptr::NonNull;
use crate::error::EmptyCollectionError;
//use core::range::RangeBounds;
use crate::NonEmpty;

#[cfg(doc)]
use alloc::borrow::ToOwned;

/// A replacement for [`Vec`] that guarantees it's not empty.
///
/// Similarly to `NonEmpty<Vec<T>>`, this guarantees that the collection is not empty but unlike
/// `NonEmpty<Vec<T>>` it also explains this to the compiler so that the property can be used in
/// layout optimizations. For instance, it's possible to implement `Cow` from the `beef` crate
/// using only safe code!
///
/// ```
/// use non_empty::vec::NonEmptyVec;
/// use core::mem::size_of;
///
/// enum Cow<'a, T> {
///     Borrowed(&'a [T]),
///     Owned(NonEmptyVec<T>),
/// }
///
/// impl<T> From<Vec<T>> for Cow<'_, T> {
///     fn from(value: Vec<T>) -> Self {
///         match NonEmptyVec::from_vec(value) {
///             Some(non_empty) => Cow::Owned(non_empty),
///             None => Cow::Borrowed(&[]),
///         }
///     }
/// }
///
/// impl<'a, T> From<&'a [T]> for Cow<'a, T> {
///     fn from(value: &'a [T]) -> Self {
///         Cow::Borrowed(value)
///     }
/// }
///
/// impl<T> core::ops::Deref for Cow<'_, T> {
///     type Target = [T];
///
///     fn deref(&self) -> &Self::Target {
///         match self {
///             Cow::Borrowed(borrowed) => borrowed,
///             Cow::Owned(owned) => owned.as_slice(),
///         }
///     }
/// }
///
/// // The layout is optimized!
/// assert_eq!(size_of::<Cow<i32>>(), size_of::<Vec<i32>>());
/// let cow = Cow::from("hello".as_bytes());
/// assert_eq!(*cow, *"hello".as_bytes());
/// let cow = Cow::from("hello".as_bytes().to_owned());
/// assert_eq!(*cow, *"hello".as_bytes());
/// let cow = Cow::<u8>::from(Vec::new());
/// assert_eq!(*cow, []);
/// ```
///
/// Notably, `NonEmpty<[T]>` also intentionally implements [`ToOwned`] such that its `Owned` type
/// is `NonEmptyVec<T>`. That means the `Cow` from `std` is already optimized *for non-empty* use
/// case.
///
/// ```
/// # extern crate alloc;
/// use non_empty::NonEmpty;
///
/// assert_eq!(size_of::<alloc::borrow::Cow<NonEmpty<[i32]>>>(), size_of::<Vec<i32>>());
/// ```
pub struct NonEmptyVec<T> {
    // Invariants:
    //  * `ptr` is always dereferencable
    //  * `len <= capacity`
    //  * All invariants implied by the individual types
    ptr: NonNull<T>,
    len: NonZeroUsize,
    capacity: NonZeroUsize,
}

impl<T> NonEmptyVec<T> {
    /// Attempts to construct `NonEmptyVec` from a possibly-empty `Vec`.
    ///
    /// Returns [`Some`] if the `vec` is non-empty or [`None`] if the `vec` is empty.
    pub fn from_vec(vec: Vec<T>) -> Option<Self> {
        NonEmpty::new(vec).map(Into::into)
    }

    /// Creates a vec and inserts an element into it.
    pub fn with_first_element(element: T) -> Self {
        NonEmpty::<Vec<T>>::with_first_element(element).into()
    }

    /// Creates a vec and inserts an element into it.
    ///
    /// This reserves `additional_capacity + 1` before inserting the element.
    ///
    /// Panics in debug mode if `additional_capacity` is `usize::MAX`.
    pub fn with_first_element_and_extra_capacity(item: T, additional_capacity: usize) -> Self {
        NonEmpty::<Vec<T>>::with_first_element_and_extra_capacity(item, additional_capacity)
            .into()
    }

    /// Reserves capacity for `additional` elements.
    pub fn reserve(&mut self, additional: usize) {
        self.with_vec(move |vec| vec.reserve(additional))
    }

    /// Attempts to reserve capacity for `additional` elements.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        // SOUNDNESS: try_reserve doesn't modify the length
        unsafe { self.with_vec_unchecked(move |vec| vec.try_reserve(additional)) }
    }

    /// Assumes that the given `vec` is not empty.
    ///
    /// # Soundness
    ///
    /// Passing in an empty `vec` causes undefined behavior. Any other value that is otherwise
    /// valid for `Vec` is valid to pass into this function.
    pub unsafe fn from_vec_unchecked(vec: Vec<T>) -> Self {
        let mut vec = ManuallyDrop::new(vec);

        NonEmptyVec {
            // SOUNDNESS: vec never contains a null pointer
            ptr: NonNull::new_unchecked(vec.as_mut_ptr()),
            // SOUNDNESS: the caller is reponsible for this to hold
            len: NonZeroUsize::new_unchecked(vec.len()),
            // SOUNDNESS: implied by Vec's invariant and caller's reponsibility
            capacity: NonZeroUsize::new_unchecked(vec.capacity()),
        }
    }

    /// Returns a pointer pointing at the beginning of the storage.
    pub fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    /// Returns a mutable pointer pointing at the beginning of the storage.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Returns a non-null pointer pointing at the beginning of the storage.
    pub fn as_non_null(&mut self) -> NonNull<T> {
        self.ptr
    }

    /// Returns the number of elements stored.
    ///
    /// As the return type suggests, this is never zero.
    pub fn len(&self) -> NonZeroUsize {
        self.len
    }

    /// Sets the length to the `new_len`.
    ///
    /// # Soundness
    ///
    /// The `new_len` must be smaller than or equal to capacity and all elements up to `new_len`
    /// must be initialized.
    pub unsafe fn set_len(&mut self, new_len: NonZeroUsize) {
        self.len = new_len;
    }

    /// Returns how many elements can be stored without reallocating.
    pub fn capacity(&self) -> NonZeroUsize {
        self.capacity
    }

    /// Removes the proof of non-emptiness.
    pub fn into_vec(self) -> Vec<T> {
        let this = ManuallyDrop::new(self);
        // SOUNDNESS: these values were previously created from a valid `Vec`.
        unsafe {
            Vec::from_raw_parts(this.ptr.as_ptr(), this.len.into(), this.capacity.into())
        }
    }

    /// Converts the layout to a more generic one.
    ///
    /// Note that this removes layout optimization and thus should be only used for intermediate
    /// operations.
    pub fn into_non_empty(self) -> NonEmpty<Vec<T>> {
        // SOUNDNESS: `self` is not empty
        unsafe { NonEmpty::new_unchecked(self.into_vec()) }
    }

    /// Borrows a slice that still proves it's not empty.
    pub fn as_non_empty_slice(&self) -> &NonEmpty<[T]> {
        // SOUNDNESS: `self` is not empty and `as_slice` returns equally long slice.
        unsafe { NonEmpty::new_ref_unchecked(self.as_slice()) }
    }

    /// Borrows a mutable slice that still proves it's not empty.
    pub fn as_mut_non_empty_slice(&mut self) -> &mut NonEmpty<[T]> {
        // SOUNDNESS: `self` is not empty and `as_mut_slice` returns equally long slice.
        unsafe { NonEmpty::new_mut_unchecked(self.as_mut_slice()) }
    }

    /// Borrows a slice without the proof that it's not empty.
    pub fn as_slice(&self) -> &[T] {
        // SOUNDNESS: The values are valid for a vec because of type's invariants and thus they
        // are valid for a slice.
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len().into()) }
    }

    /// Borrows a mutable slice without the proof that it's not empty.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SOUNDNESS: The values are valid for a vec because of type's invariants and thus they
        // are valid for a slice.
        let len = self.len().into();
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    /// Creates a temporary `Vec` holding the data and passes it to the closure.
    ///
    /// # Soundness
    ///
    /// The closure MUST NOT leave the vec empty when it returns. All other operations leaving a
    /// valid `Vec` are allowed.
    unsafe fn with_vec_unchecked<R>(&mut self, f: impl FnOnce(&mut Vec<T>) -> R) -> R {
        struct PutBack<'a, T> {
            original: &'a mut NonEmptyVec<T>,
            temp: ManuallyDrop<Vec<T>>,
        }

        impl<'a, T> Drop for PutBack<'a, T> {
            fn drop(&mut self) {
                unsafe {
                    core::ptr::write(self.original, NonEmptyVec::from_vec_unchecked(ManuallyDrop::take(&mut self.temp)));
                }
            }
        }

        let vec = ManuallyDrop::new(Vec::from_raw_parts(self.ptr.as_ptr(), self.len.into(), self.capacity.into()));
        let mut guard = PutBack {
            original: self,
            temp: vec,
        };

        f(&mut guard.temp)
    }

    pub(crate) fn with_vec<R>(&mut self, f: impl FnOnce(&mut NonEmpty<Vec<T>>) -> R) -> R {
        // SOUNDNESS: the `vec` is not empty since it was created from `self` and the wrapping type
        // ensures it stays that way.
        unsafe {
            self.with_vec_unchecked(move |vec| f(NonEmpty::new_mut_unchecked(vec)))
        }
    }

    /// Removes the elements stored in `other` and puts them at the end of `self`.
    pub fn append(&mut self, other: &mut Vec<T>) {
        // SOUNDNESS: appending values does not decrease the number of elements.
        unsafe { self.with_vec_unchecked(move |vec| vec.append(other)) }
    }

    /// Changes the number of elements, potentially producing new ones using `f`.
    ///
    /// If `new_len` is less than `self.len()` this truncates the vec (removes elements from the
    /// end). If `new_len` is equal to `self.len()` this is no-op. If `new_len` is greater than
    /// `self.len()` this produces `new_len - self.len()` elements by calling `f` repeatedly and
    /// puts them at the end.
    pub fn resize_with<F>(&mut self, new_len: NonZeroUsize, f: F) where F: FnMut() -> T {
        // SOUNDNESS: new_len is non-zero so the resulting length won't be zero either.
        unsafe { self.with_vec_unchecked(move |vec| vec.resize_with(new_len.into(), f)) }
    }

    /// Prevents destructor from running and returns a reference to a slice that's provably
    /// non-empty.
    pub fn leak<'a>(self) -> &'a mut NonEmpty<[T]> {
        // SOUNDNESS: `self` is non-empty and neither `into_vec` nor `leak` change the number of
        // elements.
        unsafe { NonEmpty::new_mut_unchecked(self.into_vec().leak()) }
    }

    /// Returns a mutable reference to the uninitialized part of the storage.
    ///
    /// This can be used with `set_len` to fill the items in `unsafe` code - usually FFI.
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        // SOUNDNESS: this is pretty much copied from `std`
        // we know `len` is in bounds for the allocation because that's the type's invariant
        unsafe {
            let len = usize::from(self.capacity()) - usize::from(self.len());
            core::slice::from_raw_parts_mut(self.as_mut_ptr().add(self.len.into()) as *mut _, len)
        }
    }

    /// Adds the `element` at the end.
    pub fn push(&mut self, element: T) {
        // SOUNDNESS: push only increases the length, never decreases
        unsafe { self.with_vec_unchecked(move |vec| vec.push(element)) }
    }

    /// Inserts the `element` at the given `index`.
    pub fn insert(&mut self, index: usize, element: T) {
        // SOUNDNESS: insert only increases the length, never decreases
        unsafe { self.with_vec_unchecked(move |vec| vec.insert(index, element)) }
    }

    /// Removes the last element and returns it together with the remaining elements.
    pub fn pop(self) -> (T, Vec<T>) {
        self.into_non_empty().pop_last()
    }

    /// Attempts to modify `self` by removing the last element.
    ///
    /// Returns `None` if the length is 1.
    pub fn try_pop(&mut self) -> Option<T> {
        self.with_vec(|vec| vec.try_pop_last())
    }

    /// Returns the element at given `index` replacing it with the last one.
    ///
    /// # Panics
    ///
    /// If `index` is greater or equal to `self.len()`
    pub fn swap_remove(self, index: usize) -> (T, Vec<T>) {
        let mut vec = self.into_vec();
        let element = vec.swap_remove(index);
        (element, vec)
    }

    /// Returns the first element at replacing it with the last one.
    ///
    /// This method always succeeds.
    pub fn swap_remove_first(self) -> (T, Vec<T>) {
        self.swap_remove(0)
    }

    /// Attempts to remove the element at given `index`.
    ///
    /// Returns an error if there is only one element or if the `index` is out of bounds.
    pub fn try_remove(&mut self, index: usize) -> Result<T, RemoveError> {
        // SOUNDNESS: the `try_remove_inner` method guarantees `self.len() > 1`
        self.try_remove_inner(index, move |vec| unsafe { vec.inner_mut().remove(index) })
    }

    /// Attempts to remove the element at given `index` and replace it with the last one.
    ///
    /// Returns an error if there is only one element or if the `index` is out of bounds.
    pub fn try_swap_remove(&mut self, index: usize) -> Result<T, RemoveError> {
        // SOUNDNESS: the `try_remove_inner` method guarantees `self.len() > 1`
        self.try_remove_inner(index, |vec| unsafe { vec.inner_mut().swap_remove(index) })
    }

    /// Checks if it's sound to remove an element at the given `index` and calls `f` if it is.
    ///
    /// It is guaranteed that removing an element at given index will not break any invariants and
    /// the `index` is less than `self.len()`.
    fn try_remove_inner(&mut self, index: usize, f: impl FnOnce(&mut NonEmpty<Vec<T>>) -> T) -> Result<T, RemoveError> {
        match (self.len().if_less_than(index), usize::from(self.len()) == 1) {
            (None, false) => {
                Ok(self.with_vec(f))
               },
            (None, true) => Err(RemoveError::WouldBecomeEmpty),
            (Some(index), false) => {
                Err(RemoveError::IndexOutOfBounds {
                    // SOUNDNESS: if vec.len() > 0 then the condition implies index > 0
                    index,
                    len: self.len()
                })
            },
            (Some(index), true) => {
                Err(RemoveError::Both {
                    // SOUNDNESS: if vec.len() > 0 then the condition implies index > 0
                    index,
                    len: self.len()
                })
            },
        }
    }

    /// Removes all elements past `len`.
    ///
    /// If `len` is greater than `self.len()` this is a no-op.
    pub fn truncate(&mut self, len: NonZeroUsize) {
        // SOUNDNESS: `len` is non-zero.
        unsafe { self.with_vec_unchecked(move |vec| { vec.truncate(len.into()) }) }
    }

    /// Removes the elements starting from `at` and moves them into a `Vec` which is then returned.
    pub fn split_off(&mut self, at: NonZeroUsize) -> Vec<T> {
        // SOUNDNESS: `at` is non-zero.
        unsafe { self.with_vec_unchecked(move |vec| { vec.split_off(at.into()) }) }
    }

    /// Deduplicates consecutive elements using custom comparison function `same_bucket`.
    pub fn dedup_by<F>(&mut self, same_bucket: F) where F: FnMut(&mut T, &mut T) -> bool {
        // SOUNDNESS: when deduplicating only the duplicate elements are removed but the first one
        // in each bucket remains so if there already was at least one there still will be.
        unsafe { self.with_vec_unchecked(move |vec| vec.dedup_by(same_bucket)) }
    }

    /// Deduplicates consecutive elements where the `key` function produces equal values.
    pub fn dedup_by_key<F, K>(&mut self, key: F) where F: FnMut(&mut T) -> K, K: PartialEq {
        unsafe { self.with_vec_unchecked(move |vec| vec.dedup_by_key(key)) }
    }

    /// Drops the excess capacity.
    pub fn shrink_to_fit(&mut self) {
        // SOUNDNESS: `shrink_to_fit` doesn't change the length.
        unsafe { self.with_vec_unchecked(move |vec| vec.shrink_to_fit()) }
    }
}

impl<T: Clone> NonEmptyVec<T> {
    /// Changes the number of elements, potentially producing new ones using `f`.
    ///
    /// If `new_len` is less than `self.len()` this truncates the vec (removes elements from the
    /// end). If `new_len` is equal to `self.len()` this is no-op. If `new_len` is greater than
    /// `self.len()` this produces `new_len - self.len()` elements by cloning `value` repeatedly
    /// and puts them at the end.
    pub fn resize(&mut self, new_len: NonZeroUsize, value: T) {
        // SOUNDNESS: `new_len` is non-zero.
        unsafe { self.with_vec_unchecked(move |vec| vec.resize(new_len.into(), value)) }
    }

    /// Clones elements in `other` and appends them.
    pub fn extend_from_slice(&mut self, other: &[T]) {
        // SOUNDNESS: adding elements doesn't decrease the number of elements.
        unsafe { self.with_vec_unchecked(move |vec| vec.extend_from_slice(other)) }
    }
}

impl<const N: usize, T> NonEmptyVec<[T; N]> {
    const CHECK: () = assert!(N != 0);

    /// Flattens a vec of arrays to just vec of values that were in those arrays.
    ///
    /// Causes a post-monomorphization error if `N` is zero.
    pub fn into_non_empty_flattened(self) -> NonEmptyVec<T> {
        let _ = Self::CHECK;
        unsafe { NonEmptyVec::from_vec_unchecked(self.into_vec().into_flattened()) }
    }
}

impl<T: PartialEq> NonEmptyVec<T> {
    /// Deduplicates consecutive elements that are equal according to `PartialEq`.
    pub fn dedup(&mut self) {
        unsafe { self.with_vec_unchecked(move |vec| vec.dedup()) }
    }
}

impl<T> core::ops::Deref for NonEmptyVec<T> {
    type Target = NonEmpty<[T]>;

    fn deref(&self) -> &Self::Target {
        self.as_non_empty_slice()
    }
}

impl<T> AsRef<NonEmpty<[T]>> for NonEmptyVec<T> {
    fn as_ref(&self) -> &NonEmpty<[T]> {
        self.as_non_empty_slice()
    }
}

impl<T> AsMut<NonEmpty<[T]>> for NonEmptyVec<T> {
    fn as_mut(&mut self) -> &mut NonEmpty<[T]> {
        self.as_mut_non_empty_slice()
    }
}

impl<T> core::borrow::Borrow<NonEmpty<[T]>> for NonEmptyVec<T> {
    fn borrow(&self) -> &NonEmpty<[T]> {
        self.as_non_empty_slice()
    }
}

impl<T> core::borrow::BorrowMut<NonEmpty<[T]>> for NonEmptyVec<T> {
    fn borrow_mut(&mut self) -> &mut NonEmpty<[T]> {
        self.as_mut_non_empty_slice()
    }
}

impl<T> core::borrow::Borrow<[T]> for NonEmptyVec<T> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> core::borrow::BorrowMut<[T]> for NonEmptyVec<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> From<NonEmpty<Vec<T>>> for NonEmptyVec<T> {
    fn from(value: NonEmpty<Vec<T>>) -> Self {
        // SOUNDNESS: the type proves vec is not empty.
        unsafe { Self::from_vec_unchecked(value.into_inner()) }
    }
}

impl<T> From<NonEmptyVec<T>> for NonEmpty<Vec<T>> {
    fn from(value: NonEmptyVec<T>) -> Self {
        value.into_non_empty()
    }
}

impl<T> From<NonEmptyVec<T>> for Vec<T> {
    fn from(value: NonEmptyVec<T>) -> Self {
        value.into_vec()
    }
}

impl<T> TryFrom<Vec<T>> for NonEmptyVec<T> {
    type Error = EmptyCollectionError;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        Self::from_vec(value).ok_or(EmptyCollectionError)
    }
}

// SOUNDNESS: We only check length in TryFromImpl
impl<T> crate::traits::FromInner for NonEmptyVec<T> {
    type Inner = Vec<T>;

    unsafe fn from_inner(inner: Self::Inner) -> Self {
        Self::from_vec_unchecked(inner)
    }
}

impl<T> crate::iter::FromNonEmptyIterator<T> for NonEmptyVec<T> {
    fn from_non_empty_iter<I: crate::iter::NonEmptyIntoIter<Item = T>>(iter: I) -> Self {
        crate::iter::from_iter_spec(iter)
    }
}

impl<T> IntoIterator for NonEmptyVec<T> {
    type Item = T;
    type IntoIter = alloc::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<T> crate::iter::NonEmptyIntoIter for NonEmptyVec<T> {
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        let mut iter = self.into_iter();
        // SOUNDNESS: non-emptiness guaranteed by type invariant
        let first = unsafe { iter.next().unwrap_unchecked() };
        (first, iter)
    }
}

impl<'a, T> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().into_iter()
    }
}

impl<'a, T> crate::iter::NonEmptyIntoIter for &'a NonEmptyVec<T> {
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        unsafe { crate::iter::into_first_and_remaining(self) }
    }
}

impl<'a, T> IntoIterator for &'a mut NonEmptyVec<T> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().into_iter()
    }
}

impl<'a, T> crate::iter::NonEmptyIntoIter for &'a mut NonEmptyVec<T> {
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        unsafe { crate::iter::into_first_and_remaining(self) }
    }
}

unsafe impl<T> crate::WellBehavedCollection for NonEmptyVec<T> {}

/// Our extension for operations not (yet) in std.
trait NonZeroUsizeExt: Sized {
    /// Checks if `self < rhs` and if it holds it returns `Some(rhs)`.
    ///
    /// The point of this function is that `rhs` being greater or equal to a non-zero `self`
    /// implies `rhs` is also non-zero and the method helps code that needs this property to prove
    /// it.
    fn if_less_than(self, rhs: usize) -> Option<NonZeroUsize>;
}

impl NonZeroUsizeExt for NonZeroUsize {
    fn if_less_than(self, rhs: usize) -> Option<NonZeroUsize> {
        if usize::from(self) < rhs {
            // SOUNDNESS: If the left side is greater than or equal to 1 then the right side has to
            // be as well.
            Some(unsafe { NonZeroUsize::new_unchecked(rhs) })
        } else {
            None
        }
    }
}

/// Error returned when removing an element fails.
#[derive(Debug, Copy, Clone)]
pub enum RemoveError {
    /// The index is greater or equal to the number of elements.
    IndexOutOfBounds {
        /// The index used for attempted access.
        index: NonZeroUsize,
        /// The total number of elements stored.
        len: NonZeroUsize,
    },
    /// Removing the element would leave an empty vec.
    WouldBecomeEmpty,
    /// Both the index is out of bounds and the vec would become empty after removing the element.
    Both {
        /// The index used for attempted access.
        index: NonZeroUsize,
        /// The total number of elements stored.
        len: NonZeroUsize,
    },
}

impl RemoveError {
    /// Returns `true` if there was out-of-bounds access.
    ///
    /// Note that this also returns `true` for the `Both` variant.
    pub fn is_oob(&self) -> bool {
        matches!(self, RemoveError::IndexOutOfBounds { .. } | RemoveError::Both { .. })
    }

    /// Returns `true` if the resulting vec would become empty after removing the element.
    ///
    /// Note that this also returns `true` for the `Both` variant.
    pub fn is_would_become_empty(&self) -> bool {
        matches!(self, RemoveError::WouldBecomeEmpty | RemoveError::Both { .. })
    }
}

impl fmt::Display for RemoveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RemoveError::IndexOutOfBounds { index, len } => {
                write!(f, "the index {} is not smaller than length {}", index, len)
            },
            RemoveError::Both { index, len } => {
                write!(f, "the collection would become empty and the index {} is not smaller than length {}", index, len)
            },
            RemoveError::WouldBecomeEmpty => {
                write!(f, "the collection would become empty")
            }
        }
    }
}

crate::error::if_std_error! {
    impl crate::error::StdError for RemoveError {}
}

