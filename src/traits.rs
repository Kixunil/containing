//! Traits abstracting collections.
//!
//! Consumers of this library that only use `std` types inside `NonEmpty` or types from other
//! crates that already implement these traits do not need to be concerned with these traits. Only
//! implementors of custom collections need to implement them.
//!
//! Note that bounding by these traits in generics outside of this crate is considered
//! second-class.

#[cfg(all(doc, feature = "std"))]
use std::path::Path;
#[cfg(all(doc, feature = "std"))]
use std::ffi::OsStr;

/// Represents collections that know their length.
pub trait Len {
    /// Returns the length of the collection.
    fn len(&self) -> usize;
}

impl Len for str {
    fn len(&self) -> usize {
        self.len()
    }
}

/// Represents collections that store `Item`.
pub trait Collection {
    /// The type stored in the collection.
    ///
    /// This is returned from methods like `first`, `last`...
    /// The value is used in case of maps, not a key-value tuple.
    // Note: the reason for this is that sometimes tuple of references is returned rather than
    // owned values. We have special methods where key-value pairs are handled.
    type Item;
}

impl crate::Collection for str {
    type Item = char;
}

/// Represents collections that can allocate some capacity upfront.
#[cfg(feature = "alloc")]
pub trait Reserve {
    /// Makes sure the collection has capacity to hold at least `capacity` additional items.
    fn reserve(&mut self, capacity: usize);

    /// Creates the collection and pre-allocates space for items.
    fn with_capacity(capacity: usize) -> Self where Self: Default {
        let mut collection = Self::default();
        collection.reserve(capacity);
        collection
    }
}

/// Any collection that can return a reference to the first (front) element.
pub trait First: Collection {
    /// Returns a shared reference to the first element.
    fn first(&self) -> Option<&Self::Item>;
}

/// Any collection that can return a mutable reference to the first (front) element.
pub trait FirstMut: First {
    /// Returns a mutable reference to the first element.
    fn first_mut(&mut self) -> Option<&mut Self::Item>;
}

/// Any collection that can return a reference to the last (back) element.
pub trait Last: Collection {
    /// Returns a shared reference to the last element.
    fn last(&self) -> Option<&Self::Item>;
}

/// Any collection that can return a mutable reference to the last (back) element.
pub trait LastMut: Collection {
    /// Returns a mutable reference to the last element.
    fn last_mut(&mut self) -> Option<&mut Self::Item>;
}

/// Any collection that can have its first (front) element removed.
pub trait PopFirst: Collection {
    /// Removes the first (front) element from the collection.
    fn pop_first(&mut self) -> Option<Self::Item>;
}

/// Any collection that can have its last (back) element removed.
pub trait PopLast: Collection {
    /// Removes the last (back) element from the collection.
    fn pop_last(&mut self) -> Option<Self::Item>;
}

/// Marks types that are slices or `Sized`.
///
/// In other words, this ensures `Self` is not a trait object (or extern type, which are unstable).
pub unsafe trait SliceOrSized {}

// SOUNDNESS: the type is `Sized` because of the implicit bound
unsafe impl<T> SliceOrSized for T {}
// SOUNDNESS: the type is a slice
unsafe impl<T> SliceOrSized for [T] {}
// SOUNDNESS: the type is a string slice
unsafe impl SliceOrSized for str {}

pub(crate) trait FromInner {
    type Inner;

    unsafe fn from_inner(inner: Self::Inner) -> Self;
}

/// Marker for collections that cannot have their length changed even using `&mut`.
///
/// These are arrays, slices, [`str`], [`OsStr`], [`Path`]. It's allowed to take a mutable
/// reference to these even when they are inside `NonEmpty`.
pub unsafe trait FixedLenCollection {}

// SOUNDNESS: &mut [T] cannot change the length, only create a new, shorter reference which is fine
// since it doesn't update the original. We specifially do NOT implement this for references
// because then the change would become possible.
unsafe impl<T> FixedLenCollection for [T] {}
// SOUNDNESS: the length is defined by the type and that cannot change during run time.
unsafe impl<const N: usize, T> FixedLenCollection for [T; N] {}
// SOUNDNESS: the length is defined by the type and that cannot change during run time even for
// references.
unsafe impl<const N: usize, T> FixedLenCollection for &'_ [T; N] {}
// SOUNDNESS: the length is defined by the type and that cannot change during run time even for
// references.
unsafe impl<const N: usize, T> FixedLenCollection for &'_ mut [T; N] {}
// SOUNDNESS: &mut str cannot change the length, only create a new, shorter reference which is fine
// since it doesn't update the original. We specifially do NOT implement this for references
// because then the change would become possible.
unsafe impl FixedLenCollection for str {}
