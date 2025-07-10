//! Specialized types for non-empty slices.
//!
//! These types are replacements for `&[T]` and `&mut T` with the only difference being that their
//! length field is stored as `NonZeroUsize` communicating to the compiler that the field is always
//! non-zero. As a result, you might get better performance using these. Note however that this
//! will likely only be the case in niche cases such as storing a lot of
//! `Option<NonEmptySlice<'a, T>>`. In general it's recommended to start with `NonEmpty<[T]>`
//! first, which has a bit nicer API and only switch to these types when profiling proves it
//! beneficial.
//!
//! Hopefully, it'll be possible to implement these as an optimization of `NonEmpty` at some point
//! in the future (with specialization and custom DST) in which case these will get deprecated.

use crate::NonEmpty;
use core::ptr::NonNull;
use core::num::NonZeroUsize;
use core::marker::PhantomData;

#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;

/// An equivalent of `&'a NonEmpty<[T]>` with `NonZeroUsize` field.
///
/// See the module documentation for details.
pub struct NonEmptySlice<'a, T> {
    ptr: NonNull<T>,
    len: NonZeroUsize,
    _phantom: PhantomData<&'a [T]>,
}

impl<'a, T> Copy for NonEmptySlice<'a, T> {}
impl<'a, T> Clone for NonEmptySlice<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<'a, T> Send for NonEmptySlice<'a, T> where &'a [T]: Send {}
unsafe impl<'a, T> Sync for NonEmptySlice<'a, T> where &'a [T]: Sync {}

impl<'a, T> NonEmptySlice<'a, T> {
    /// Converts the slice.
    pub fn new(slice: &'a NonEmpty<[T]>) -> Self {
        unsafe {
            Self {
                // SOUNDNESS: the slice pointer is never null
                ptr: NonNull::new_unchecked(slice.as_inner().as_ptr() as *mut _),
                len: slice.len(),
                _phantom: PhantomData,
            }
        }
    }

    /// Returns a shared reference to the ordinary slice.
    pub fn to_slice(self) -> &'a [T] {
        unsafe {
            core::slice::from_raw_parts(self.ptr.as_ptr(), self.len.into())
        }
    }

    /// Returns a shared reference to the ordinary slice wrapped in `NonEmpty`.
    pub fn to_non_empty_slice(self) -> &'a NonEmpty<[T]> {
        unsafe {
            NonEmpty::new_ref_unchecked(self.to_slice())
        }
    }

    /// Allocates a non-empty vec and clones all elements into it.
    ///
    /// The resulting vec is guaranteed to be non-empty and this is proven by the type.
    #[cfg(feature = "alloc")]
    pub fn to_non_empty_vec(&self) -> crate::vec::NonEmptyVec<T> where T: Clone {
        self.to_non_empty_slice().to_owned()
    }
}

impl<'a, T> From<&'a NonEmpty<[T]>> for NonEmptySlice<'a, T> {
    fn from(value: &'a NonEmpty<[T]>) -> Self {
        Self::new(value)
    }
}

impl<'a, T> From<NonEmptySlice<'a, T>> for &'a NonEmpty<[T]> {
    fn from(value: NonEmptySlice<'a, T>) -> Self {
        value.to_non_empty_slice()
    }
}

impl<T> AsRef<NonEmpty<[T]>> for NonEmptySlice<'_, T> {
    fn as_ref(&self) -> &NonEmpty<[T]> {
        self.to_non_empty_slice()
    }
}

impl<T> AsRef<[T]> for NonEmptySlice<'_, T> {
    fn as_ref(&self) -> &[T] {
        self.to_slice()
    }
}

impl<T> core::borrow::Borrow<NonEmpty<[T]>> for NonEmptySlice<'_, T> {
    fn borrow(&self) -> &NonEmpty<[T]> {
        self.to_non_empty_slice()
    }
}

impl<T> core::borrow::Borrow<[T]> for NonEmptySlice<'_, T> {
    fn borrow(&self) -> &[T] {
        self.to_slice()
    }
}

/// An equivalent of `&'a mut NonEmpty<[T]>` with `NonZeroUsize` field.
///
/// See the module documentation for details.
pub struct NonEmptyMutSlice<'a, T> {
    ptr: NonNull<T>,
    len: NonZeroUsize,
    _phantom: PhantomData<&'a mut [T]>,
}

unsafe impl<'a, T> Send for NonEmptyMutSlice<'a, T> where &'a mut [T]: Send {}
unsafe impl<'a, T> Sync for NonEmptyMutSlice<'a, T> where &'a mut [T]: Sync {}

impl<'a, T> NonEmptyMutSlice<'a, T> {
    /// Converts the slice.
    pub fn new(slice: &'a mut NonEmpty<[T]>) -> Self {
        unsafe {
            let len = slice.len();
            Self {
                // SOUNDNESS: the slice pointer is never null
                ptr: NonNull::new_unchecked(slice.as_inner_mut().as_mut_ptr()),
                // SOUNDNESS: guaranteed by the `NonZero` invariant
                len,
                _phantom: PhantomData,
            }
        }
    }

    /// Returns an ordinary ("possibly empty") slice.
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            core::slice::from_raw_parts(self.ptr.as_ptr(), self.len.into())
        }
    }

    /// Returns an ordinary ("possibly empty") mutable slice.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            core::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len.into())
        }
    }

    /// Converts this type into an ordinary mutable slice.
    ///
    /// As opposed to `as_mut_slice` this doesn't perform reborrow so the lifetime is preserved.
    pub fn into_mut_slice(self) -> &'a mut [T] {
        unsafe {
            core::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len.into())
        }
    }

    /// Returns a sharedd reference to an ordinary slice wrapped in `NonEmpty`.
    pub fn as_non_empty_slice(&self) -> &NonEmpty<[T]> {
        unsafe {
            NonEmpty::new_ref_unchecked(self.as_slice())
        }
    }

    /// Returns a mutable reference to ordinary slice wrapped in `NonEmpty`.
    pub fn as_mut_non_empty_slice(&mut self) -> &mut NonEmpty<[T]> {
        unsafe {
            NonEmpty::new_mut_unchecked(self.as_mut_slice())
        }
    }

    /// Converts this type into an ordinary slice wrapped in `NonEmpty`.
    ///
    /// As opposed to `as_mut_slice` this doesn't perform reborrow so the lifetime is preserved.
    pub fn into_non_empty_mut_slice(self) -> &'a mut NonEmpty<[T]> {
        unsafe {
            NonEmpty::new_mut_unchecked(self.into_mut_slice())
        }
    }
}

impl<'a, T> From<&'a mut NonEmpty<[T]>> for NonEmptyMutSlice<'a, T> {
    fn from(value: &'a mut NonEmpty<[T]>) -> Self {
        Self::new(value)
    }
}

impl<'a, T> From<NonEmptyMutSlice<'a, T>> for &'a mut NonEmpty<[T]> {
    fn from(value: NonEmptyMutSlice<'a, T>) -> Self {
        value.into_non_empty_mut_slice()
    }
}

impl<T> AsRef<NonEmpty<[T]>> for NonEmptyMutSlice<'_, T> {
    fn as_ref(&self) -> &NonEmpty<[T]> {
        self.as_non_empty_slice()
    }
}

impl<T> AsMut<NonEmpty<[T]>> for NonEmptyMutSlice<'_, T> {
    fn as_mut(&mut self) -> &mut NonEmpty<[T]> {
        self.as_mut_non_empty_slice()
    }
}

impl<T> AsRef<[T]> for NonEmptyMutSlice<'_, T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> AsMut<[T]> for NonEmptyMutSlice<'_, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> core::borrow::Borrow<NonEmpty<[T]>> for NonEmptyMutSlice<'_, T> {
    fn borrow(&self) -> &NonEmpty<[T]> {
        self.as_non_empty_slice()
    }
}

impl<T> core::borrow::BorrowMut<NonEmpty<[T]>> for NonEmptyMutSlice<'_, T> {
    fn borrow_mut(&mut self) -> &mut NonEmpty<[T]> {
        self.as_mut_non_empty_slice()
    }
}

impl<T> core::borrow::Borrow<[T]> for NonEmptyMutSlice<'_, T> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> core::borrow::BorrowMut<[T]> for NonEmptyMutSlice<'_, T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}
