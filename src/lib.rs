//! Non-empty collections.
//!
//! **Warning: this is a preview version that is not tested yet!** It mainly intends to showcase
//! the desired API. If you want to contribute tests please feel free to do so on GitHub!
//!
//! It's quite common for algorithms to require that a certain collection is not empty.
//! For example, computing average of numbers requires that there is at least one number.
//! Rather than checking the inputs in function that computes it one might want to pass this
//! responsibility to the caller and push validation to the edge of the application.
//! This makes error reporting simpler or, in case the number of elements is statically known,
//! avoids errors completely.
//!
//! This crate provides the [`NonEmpty`] type which proves that the collection it stores is not
//! empty (assuming the collection is implemented correctly).
//! It also provides various methods and trait impls that take advantage of the invariant.
//! For instance it has the [`first`](NonEmpty::first) method that replaces those on `std`'s
//! collections such that it returns the element without being wrapped in `Option`.
//!
//! In addition, the crate provides some specialized types which use
//! [`NonZeroUsize`] internally to explain the invariant to the compiler. These can be used in data
//! structures to reduce the size of enums. As an example, one can re-implement `Cow` from the
//! [`beef`](https://docs.rs/beef) crate using only safe code thanks to this invariant.
//!
//! The API strives to be similar to that of `std` types, however there are some differences
//! between them that this crate erases to a degree.
//!
//! # Examples
//!
//! Compute average
//!
//! ```
//! use non_empty::NonEmpty;
//!
//! pub fn compute_average(numbers: &NonEmpty<[usize]>) -> usize {
//!     // This can still overflow but the type at least catches obvious mistake
//!     numbers.iter().sum::<usize>() / numbers.len()
//! }
//!
//! assert_eq!(compute_average([42, 24].as_ref()), 33);
//! ```
//!
//! However, this would fail to compile:
//!
//! ```compile_fail
//! # use non_empty::NonEmpty;
//! # 
//! # pub fn compute_average(numbers: &NonEmpty<[usize]>) -> usize {
//! #     numbers.iter().sum::<usize>() / numbers.len()
//! # }
//! #
//! assert_eq!(compute_average([].as_ref()), 42);
//! ```
//!
//! Of course, the number of items is not always known. But that's also easy to deal with:
//!
//! ```
//! # use non_empty::NonEmpty;
//! # 
//! # pub fn compute_average(numbers: &NonEmpty<[usize]>) -> usize {
//! #     numbers.iter().sum::<usize>() / numbers.len()
//! # }
//! #
//! # fn get_user_input() -> Result<Vec<usize>, Error> {
//! #     Ok(vec![42])
//! # }
//! #
//! # fn main() -> Result<(), Error> {
//!
//! let user_input = get_user_input()?;
//! let user_input = NonEmpty::new(user_input).ok_or(Error::EmptyInput)?;
//! let average = compute_average(&user_input);
//! println!("{}", average);
//!
//! #     assert_eq!(average, 42);
//! #     Ok(())
//! # }
//! #
//! # #[derive(Debug)]
//! # enum Error {
//! #     EmptyInput,
//! # }
//! ```
//!
//! Note that you don't always have to do manual validation like this. For instance, if you're
//! using [`serde`], you can just wrap your type in [`NonEmpty`] and it'll validate the length for
//! you! Similarly, you can use `string.parse()` if the collection implements
//! [`FromStr`](core::str::FromStr) or use [`configure_me`](https://docs.rs/confiure_me) out of the
//! box if the collection implements `ParseArg` (this works well for strings).
//!
//! # Features
//!
//! * `std` - enables support for [`std`] types. On by default, implies `alloc`.
//! * `alloc` - enables support for [`alloc`] types. On by defult, implied by `std`.
//! * `parse_arg` - implements the [`parse_arg::ParseArg`] trait.
//! * `serde` - implements [`serde::Serialize`] and [`serde::Deserialize`].
//! * `newer-rust` - enables rust version detection and thus features requiring higher MSRV. This
//!   may or may not add a dependency (currently it does) and may become deprecated once version
//!   checking is supported by Rust itself.
//!
//! # Why this crate contains (so much) `unsafe`?
//!
//! If you look at the code there appear to be many lines of `unsafe`. However, almost all boil down
//! to "this collection is not empty" which is a trivial condition/assumption. We're trusting
//! [`std`] to implement its types properly (no logic bugs in collections) and this is indicated by
//! the `WellBehavedCollection` trait. However, non-`std` types are not trusted and the optimization
//! is not applied.
//!
//! It could be argued that the crate could've went with just panics instead. Perhaps. But it feels
//! like it'd really suck not getting use of this invariant. It'd be possible to add later but it
//! might lead the API design to not account for it which would make it difficult to add later.
//! Note though that the `unsafe` optimizations are currently turned off by default since there
//! wasn't much testing. They can be turned on with *unstable* `non_empty_no_paranoid_checks` cfg
//! flag for the time being. This will become the default (or maybe the only) option once the crate
//! is tested more.
//!
//! # Comparison with other crates
//!
//! There are other crates around that provide a similar functionality. The main advantages of this
//! one are:
//!
//! * Generic type supports arbitrary collections including the entire `std`
//! * Rich safe API
//! * Explicitly conservative MSRV
//! * Focus on getting stable and production-ready ~soon
//! * Both thin wrapper and customized types with different trade-offs
//! * Non-empty iterator API with combinators supports infallibly transforming the collections
//! * Not abandoned (yet :D)
//!
//! # MSRV
//!
//! The miminal supported Rust version is 1.63. The intention is to support the latest Debian stable
//! and, if feasible, support compilers up to two years old. The crate still supports newer rust
//! features using the `newer-rust` Cargo feature flag.
//!
//! Note that dependencies may have a more lax MSRV. This is not a bug.
//!
//! # License
//!
//! MITNFA

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![warn(missing_docs)]

use core::num::NonZeroUsize;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

pub mod error;
pub mod iter;
pub mod slice;
pub mod traits;
#[cfg(feature = "alloc")]
pub mod vec;

use traits::*;

use core::fmt;

macro_rules! impl_collection {
    ($($ty:ty),*) => {
        $(
            impl<T> crate::Collection for $ty {
                type Item = T;
            }

            impl<T> crate::Len for $ty {
                fn len(&self) -> usize {
                    <$ty>::len(self)
                }
            }
        )*
    }
}
use impl_collection;

macro_rules! delegate_first_shared_and_co {
    (<T$(: $bound:path)? $(, const $const:ident)?> $ty:ty) => {
        impl<$(const $const: usize,)? T$(: $bound)?> crate::First for $ty {
            fn first(&self) -> Option<&Self::Item> {
                self.iter().next()
            }
        }

        impl<$(const $const: usize,)? T$(: $bound)?> crate::Last for $ty {
            fn last(&self) -> Option<&Self::Item> {
                self.iter().next_back()
            }
        }
    }
}
use delegate_first_shared_and_co;

macro_rules! delegate_first_and_co {
    (<T$(: $bound:path)? $(, const $const:ident)?> $ty:ty) => {
        crate::delegate_first_shared_and_co!(<T$(: $bound)? $(, const $const)?> $ty);

        impl<$(const $const: usize,)? T$(: $bound)?> crate::FirstMut for $ty {
            fn first_mut(&mut self) -> Option<&mut Self::Item> {
                self.iter_mut().next()
            }
        }

        impl<$(const $const: usize,)? T$(: $bound)?> crate::LastMut for $ty {
            fn last_mut(&mut self) -> Option<&mut Self::Item> {
                self.iter_mut().next_back()
            }
        }
    }
}
use delegate_first_and_co;

#[cfg(feature = "alloc")]
mod alloc_impls;
#[cfg(feature = "std")]
mod std_impls;

pub use non_empty::NonEmpty;

mod non_empty {
    /// A non-empty collection.
    ///
    /// This struct is usable with any type implementing the appropriate collection traits. In
    /// particular, these `std` types already do so:
    ///
    /// * `[U]`
    /// * `[U; N]` where `N > 0`.
    /// * `Vec<U>`
    /// * `HashSet<U>`
    /// * `BTreeSet<U>`
    /// * `HashMap<U, V>`
    /// * `BTreeMap<U, V>`
    /// * `VecDeque<U>`
    /// * `&T`
    /// * `&mut T`
    /// * `Box<T>`
    /// * `Rc<T>`
    /// * `Arc<T>`
    /// * `str`
    /// * `String`
    ///
    /// Please note that while various references are supported inside the wrapper it's considered
    /// more idiomatic to use outer references instead. That means instead of `NonEmpty<&T>` you'd
    /// write `&NonEmpty<T>`. This style makes some patterns more convenient. The type has methods
    /// to cast the references as needed.
    #[repr(transparent)]
    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub struct NonEmpty<T: ?Sized>(T);

    impl<T> NonEmpty<T> {
        /// Creates the type without length checks.
        ///
        /// # Safety
        ///
        /// The `collection` MUST NOT be empty. Passing an empty collection is library UB.
        // If `T` doesn't implement `WellBehavedCollection` calling this is always sound. (But
        // should not be empty anyway for correctness.)
        pub(crate) const unsafe fn new_unchecked(collection: T) -> Self {
            Self(collection)
        }

        /// Extracts the underlying collection.
        pub fn into_inner(self) -> T {
            self.0
        }
    }

    impl<T: ?Sized> NonEmpty<T> {
        pub(crate) const fn as_inner(&self) -> &T {
            &self.0
        }

        pub(crate) unsafe fn inner_mut(&mut self) -> &mut T {
            &mut self.0
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Printing the `NonEmpty` wrapper around the collection is not useful - it obviously is
        // non-empty when printed.
        fmt::Debug::fmt(self.as_inner(), f)
    }
}

impl<T: fmt::Display> fmt::Display for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_inner(), f)
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(self.as_inner(), f)
    }
}

impl<T: fmt::UpperHex> fmt::UpperHex for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::UpperHex::fmt(self.as_inner(), f)
    }
}

impl<T: fmt::Binary> fmt::Binary for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Binary::fmt(self.as_inner(), f)
    }
}

impl<T: fmt::Octal> fmt::Octal for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Octal::fmt(self.as_inner(), f)
    }
}

impl<T: fmt::Pointer> fmt::Pointer for NonEmpty<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(self.as_inner(), f)
    }
}

impl<T: ?Sized> NonEmpty<T> {
    pub(crate) fn as_inner_mut(&mut self) -> &mut T where T: traits::FixedLenCollection {
        // SOUNDNESS: guaranteed by the trait
        unsafe { self.inner_mut() }
    }

    /// Returns an iterator over the elements of the collection.
    ///
    /// The returned iterator is guaranteed to not be empty but this is not reflected in the type.
    /// For type-safe non-empty iteration use the `into_first_and_remaining` method instead.
    pub fn iter<'a>(&'a self) -> <&'a T as IntoIterator>::IntoIter where &'a T: IntoIterator {
        self.as_inner().into_iter()
    }

    /// Returns an iterator over the mutable elements of the collection.
    ///
    /// The returned iterator is guaranteed to not be empty but this is not reflected in the type.
    /// For type-safe non-empty iteration use the `into_first_and_remaining` method instead.
    pub fn iter_mut<'a>(&'a mut self) -> <&'a mut T as IntoIterator>::IntoIter where &'a mut T: IntoIterator {
        // SOUNDNESS: converting a mutable reference to iterator doesn't modify the size of the
        // original collection.
        unsafe {
            self.inner_mut().into_iter()
        }
    }
}

impl<const N: usize, T> NonEmpty<[T; N]> {
    /// Constructs `NonEmpty` from an array.
    ///
    /// Causes post-monomorphization error if the array is empty.
    ///
    /// This may look silly, since an array is already statically known to be non-epty but it's
    /// useful to create slices using unsizing. This way you can e.g. get a slice that can have
    /// variable length and is backed by an array:
    ///
    /// ```
    /// # use non_empty::NonEmpty;
    /// # let condition = true;
    /// let slice: &NonEmpty<[_]> = if condition {
    ///     &NonEmpty::from_array([42; 1])
    /// } else {
    ///     &NonEmpty::from_array([42; 2])
    /// };
    ///
    /// # let _ = slice;
    /// ```
    pub const fn from_array(array: [T; N]) -> Self {
        let () = IsNonZero::<N>::CHECK;
        // SOUNDNESS: we've checked that N is not zero
        unsafe { Self::new_unchecked(array) }

    }

    /// Constructs a reference to `NonEmpty` from a reference to an array.
    ///
    /// Causes post-monomorphization error if the array is empty.
    ///
    /// See [`from_array`](NonEmpty::from_array) for usage explanation.
    pub const fn from_array_ref(array: &[T; N]) -> &Self {
        let () = IsNonZero::<N>::CHECK;
        // SOUNDNESS: we've checked that N is not and the layouts match
        unsafe { &*(array as *const [T; N] as *const NonEmpty<[T; N]>) }
    }

    /// Constructs a mutable reference to `NonEmpty` from a mutable reference to an array.
    ///
    /// Causes post-monomorphization error if the array is empty.
    ///
    /// See [`from_array`](NonEmpty::from_array) for usage explanation.
    pub fn from_array_mut(array: &mut [T; N]) -> &mut Self {
        let () = IsNonZero::<N>::CHECK;
        // SOUNDNESS: we've checked that N is not and the layouts match
        unsafe { &mut *(array as *mut [T; N] as *mut NonEmpty<[T; N]>) }
    }

    /// Constructs a reference to `NonEmpty` from a reference to an array.
    ///
    /// Causes post-monomorphization error if the array is empty.
    ///
    /// See [`from_array`](NonEmpty::from_array) for usage explanation.
    #[cfg(feature = "alloc")]
    pub fn from_boxed_array(array: alloc::boxed::Box<[T; N]>) -> alloc::boxed::Box<Self> {
        use alloc::boxed::Box;

        let () = IsNonZero::<N>::CHECK;
        // SOUNDNESS: we've checked that N is not and the layouts match
        unsafe { Box::from_raw(Box::into_raw(array) as *mut NonEmpty<[T; N]>) }
    }
}

impl<T> NonEmpty<T> {
    /// Checks if a collection is non-empty and returns a proof if it is.
    pub fn new(collection: T) -> Option<Self> where T: Len {
        if collection.len() != 0 {
            Some(unsafe { Self::new_unchecked(collection) })
        } else {
            None
        }
    }

    /// Creates a collection and inserts an element into it.
    pub fn with_first_element<I>(element: I) -> Self where T: Default + Extend<I> {
        let mut this = T::default();
        this.extend(core::iter::once(element));
        // SOUNDNESS: We're using extend above and `WellBehavedCollection` asserts that `Extend` is
        // working correctly
        unsafe { Self::new_unchecked(this) }
    }

    /// Creates a collection and inserts an element into it.
    ///
    /// This reserves `additional_capacity + 1` before inserting the element.
    ///
    /// Panics in debug mode if `additional_capacity` is `usize::MAX`.
    #[track_caller]
    #[cfg(feature = "alloc")]
    pub fn with_first_element_and_extra_capacity<I>(element: I, additional_capacity: usize) -> Self where T: Default + Extend<I> + Reserve {
        let mut this = T::default();
        this.reserve(additional_capacity + 1);
        this.extend(core::iter::once(element));
        // SOUNDNESS: We're using extend above and `WellBehavedCollection` asserts that `Extend` is
        // working correctly
        unsafe { Self::new_unchecked(this) }
    }

    /// Pre-allocates space for `additional` elements.
    #[cfg(feature = "alloc")]
    pub fn reserve(&mut self, additional: usize) where T: Reserve {
        unsafe { self.inner_mut().reserve(additional) }
    }

    /// Splits the collection into last element and an iterator of remaining elements.
    ///
    /// Note that the the iterator iterates from the front. You can call `.rev` to reverse it.
    pub fn into_last_and_remaining(self) -> (T::Item, T::IntoIter) where T: IntoIterator, T::IntoIter: DoubleEndedIterator {
        let mut iter = self.into_inner().into_iter();
        let first = unsafe { unwrap_opt::<T, _>(iter.next_back()) };
        (first, iter)
    }

    /// Removes the first element from the collection.
    ///
    /// This converts the type of the collection because the resulting one might be empty after the
    /// element is removed. If you wish to keep the last element in the collection call
    /// [`try_pop_first`](Self::try_pop_first).
    pub fn pop_first(self) -> (T::Item, T) where T: PopFirst + Len {
        let mut inner = self.into_inner();
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        let first = unsafe { unwrap_opt::<T, _>(inner.pop_first()) };
        (first, inner)
    }

    /// Removes the last element from the collection.
    ///
    /// This converts the type of the collection because the resulting one might be empty after the
    /// element is removed. If you wish to keep the last element in the collection call
    /// [`try_pop_last`](Self::try_pop_last).
    pub fn pop_last(self) -> (T::Item, T) where T: PopLast + Len {
        let mut inner = self.into_inner();
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        let last = unsafe { unwrap_opt::<T, _>(inner.pop_last()) };
        (last, inner)
    }
}

impl<T: ?Sized> NonEmpty<T> {
    /// Checks if a collection behind shared reference is non-empty and returns a proof if it is.
    pub fn new_ref(collection: &T) -> Option<&Self> where T: Len + SliceOrSized {
        if collection.len() != 0 {
            Some(unsafe { Self::new_ref_unchecked(collection) })
        } else {
            None
        }
    }

    /// Marks the given collection as non-empty without any checks.
    ///
    /// This can be used if the collection is known to be non-empty and the check should be
    /// avoided.
    ///
    /// # Safety
    ///
    /// This function is `unsafe` because constructing the type with empty collection is library
    /// UB. The `collection` must NOT be empty.
    pub unsafe fn new_ref_unchecked(collection: &T) -> &Self {
        &*(collection as *const T as *const NonEmpty<T>)
    }

    /// Checks if a collection behind mutable reference is non-empty and returns a proof if it is.
    pub fn new_mut(collection: &mut T) -> Option<&mut Self> where T: Len + SliceOrSized {
        if collection.len() != 0 {
            Some(unsafe { Self::new_mut_unchecked(collection) })
        } else {
            None
        }
    }

    /// Marks the given collection as non-empty without any checks.
    ///
    /// This can be used if the collection is known to be non-empty and the check should be
    /// avoided.
    ///
    /// # Safety
    ///
    /// This function is `unsafe` because constructing the type with empty collection is library
    /// UB. The `collection` must NOT be empty.
    pub unsafe fn new_mut_unchecked(collection: &mut T) -> &mut Self {
        unsafe { &mut *(collection as *mut T as *mut NonEmpty<T>) }
    }

    /// Returns the length of the collection.
    ///
    /// The returned type proves the collection is never empty.
    pub fn len(&self) -> NonZeroUsize where T: Len {
        unsafe { unwrap_opt::<T, _>(NonZeroUsize::new(self.as_inner().len())) }
    }

    /// Returns a shared reference to the first element in the collection.
    ///
    /// This is available for all ordered collections - that is all `std` collections except
    /// `HashSet` and `HashMap`.
    pub fn first(&self) -> &T::Item where T: First {
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<T, _>(self.as_inner().first()) }
    }

    /// Returns a mutable reference to the first element in the collection.
    ///
    /// This is available for all stably ordered collections - that is all `std` collectionsexcept
    /// `HashSet`, `HashMap`, and `BTreeSet`.
    pub fn first_mut(&mut self) -> &mut T::Item where T: FirstMut {
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<T, _>(self.inner_mut().first_mut()) }
    }

    /// Returns a shared reference to the last element in the collection.
    ///
    /// This is available for all ordered collections - that is all `std` collections except
    /// `HashSet` and `HashMap`.
    pub fn last(&self) -> &T::Item where T: Last {
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<T, _>(self.as_inner().last()) }
    }

    /// Returns a mutable reference to the last element in the collection.
    ///
    /// This is available for all ordered collections - that is all `std` collections except
    /// `HashSet` and `HashMap`.
    pub fn last_mut(&mut self) -> &mut T::Item where T: LastMut {
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<T, _>(self.inner_mut().last_mut()) }
    }

    /// Removes the first element in the collection and returns it if the collection has at least
    /// two elements.
    pub fn try_pop_first(&mut self) -> Option<T::Item> where T: PopFirst + Len {
        if self.as_inner().len() >= 2 {
            // SOUNDNESS: we've checked that the length is large enough to not leave `self` empty
            unsafe { self.inner_mut().pop_first() }
        } else {
            None
        }
    }


    /// Removes the last element in the collection and returns it if the collection has at least
    /// two elements.
    pub fn try_pop_last(&mut self) -> Option<T::Item> where T: PopLast + Len {
        if self.as_inner().len() >= 2 {
            // SOUNDNESS: we've checked that the length is large enough to not leave `self` empty
            unsafe { self.inner_mut().pop_last() }
        } else {
            None
        }
    }

    /// Returns the first character of a string.
    pub fn first_char(&self) -> char where T: AsRef<str> + Collection<Item=char> {
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<T, _>(self.as_inner().as_ref().chars().next()) }
    }

    /// Returns the last character of a string.
    pub fn last_char(&self) -> char where T: AsRef<str> + Collection<Item=char> {
        // SOUNDNESS: `T` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<T, _>(self.as_inner().as_ref().chars().next_back()) }
    }
}

impl<T> NonEmpty<[T]> {
    /// Returns a reference to the first element and a slice of the remaining elements.
    pub fn split_first(&self) -> (&T, &[T]) {
        // SOUNDNESS: `[T]` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<[T], _>(self.as_inner().split_first()) }
    }

    /// Returns a mutable reference to the first element and a slice of the remaining elements.
    pub fn split_first_mut(&mut self) -> (&mut T, &mut [T]) {
        // SOUNDNESS: `[T]` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<[T], _>(self.inner_mut().split_first_mut()) }
    }

    /// Returns a reference to the last element and a slice of the remaining elements.
    pub fn split_last(&self) -> (&T, &[T]) {
        // SOUNDNESS: `[T]` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<[T], _>(self.as_inner().split_last()) }
    }

    /// Returns a mutable reference to the last element and a slice of the remaining elements.
    pub fn split_last_mut(&mut self) -> (&mut T, &mut [T]) {
        // SOUNDNESS: `[T]` is the collection we are storing and we are non-empty.
        unsafe { unwrap_opt::<[T], _>(self.inner_mut().split_last_mut()) }
    }
}

impl<T: core::ops::Deref> core::ops::Deref for NonEmpty<T> where T::Target: SliceOrSized {
    type Target = NonEmpty<T::Target>;

    fn deref(&self) -> &Self::Target {
        // SOUNDNESS: WellBehavedCollection requires that non-empty container derefs to non-empty
        // target and types without it will at worst panic.
        unsafe { NonEmpty::new_ref_unchecked(self.as_inner()) }
    }
}

impl<T: core::ops::DerefMut> core::ops::DerefMut for NonEmpty<T> where T::Target: SliceOrSized {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SOUNDNESS: WellBehavedCollection requires that non-empty container derefs to non-empty
        // target and types without it will at worst panic.
        unsafe { NonEmpty::new_mut_unchecked(self.inner_mut()) }
    }
}

impl<T: ?Sized> AsRef<T> for NonEmpty<T> {
    fn as_ref(&self) -> &T {
        self.as_inner()
    }
}

impl<const N: usize, T> AsRef<NonEmpty<[T]>> for [T; N] {
    fn as_ref(&self) -> &NonEmpty<[T]> {
        NonEmpty::from_array_ref(self)
    }
}

impl<const N: usize, T> AsMut<NonEmpty<[T]>> for [T; N] {
    fn as_mut(&mut self) -> &mut NonEmpty<[T]> {
        NonEmpty::from_array_mut(self)
    }
}

impl<const N: usize, T> core::borrow::Borrow<NonEmpty<[T]>> for [T; N] {
    fn borrow(&self) -> &NonEmpty<[T]> {
        NonEmpty::from_array_ref(self)
    }
}

impl<const N: usize, T> core::borrow::BorrowMut<NonEmpty<[T]>> for [T; N] {
    fn borrow_mut(&mut self) -> &mut NonEmpty<[T]> {
        NonEmpty::from_array_mut(self)
    }
}

impl<T: traits::FixedLenCollection + ?Sized> AsMut<T> for NonEmpty<T> {
    fn as_mut(&mut self) -> &mut T {
        self.as_inner_mut()
    }
}

impl<T: ?Sized> core::borrow::Borrow<T> for NonEmpty<T> {
    fn borrow(&self) -> &T {
        self.as_inner()
    }
}

impl<T: traits::FixedLenCollection + ?Sized> core::borrow::BorrowMut<T> for NonEmpty<T> {
    fn borrow_mut(&mut self) -> &mut T {
        self.as_inner_mut()
    }
}

impl<T: PartialEq> PartialEq<T> for NonEmpty<T> {
    fn eq(&self, other: &T) -> bool {
        self.as_inner() == other
    }
}

impl<T: PartialOrd> PartialOrd<T> for NonEmpty<T> {
    fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
        self.as_inner().partial_cmp(other)
    }
}

#[cfg(feature = "alloc")]
impl<T> alloc::borrow::ToOwned for NonEmpty<[T]> where T: Clone {
    type Owned = vec::NonEmptyVec<T>;

    fn to_owned(&self) -> Self::Owned {
        unsafe {
            vec::NonEmptyVec::from_vec_unchecked(self.as_inner().to_vec())
        }
    }
}

impl<T> traits::FromInner for NonEmpty<T> {
    type Inner = T;

    #[inline]
    unsafe fn from_inner(inner: Self::Inner) -> Self {
        Self::new_unchecked(inner)
    }
}

impl<T, Item> iter::FromNonEmptyIterator<Item> for NonEmpty<T> where T: FromIterator<Item> {
    fn from_non_empty_iter<I: iter::NonEmptyIntoIter<Item = Item>>(iter: I) -> Self {
        iter::from_iter_spec(iter)
    }
}

impl<T> IntoIterator for NonEmpty<T> where T: IntoIterator {
    type Item = T::Item;
    type IntoIter = T::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.into_inner().into_iter()
    }
}

impl<T> iter::NonEmptyIntoIter for NonEmpty<T> where T: IntoIterator {
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        unsafe { iter::into_first_and_remaining(self) }
    }
}

impl<'a, T> IntoIterator for &'a NonEmpty<T> where &'a T: IntoIterator {
    type Item = <&'a T as IntoIterator>::Item;
    type IntoIter = <&'a T as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.as_inner().into_iter()
    }
}

// weirdly, From<NonEmpty<T>> for T is impossible and so is the reverse TryFrom

macro_rules! impl_refs {
    (impl<T $(: $bound:path)?> $trait:ident for SmartPtr<T> $($body:tt)+) => {
        impl<T $(: $bound)? + ?Sized> $trait for &T $($body)+
        #[cfg(feature = "alloc")]
        impl<T $(: $bound)? + ?Sized> $trait for alloc::rc::Rc<T> $($body)+
        #[cfg(feature = "alloc")]
        #[cfg(target_has_atomic = "ptr")]
        impl<T $(: $bound)? + ?Sized> $trait for alloc::sync::Arc<T> $($body)+
        impl_mut_refs! {
            impl<T $(: $bound)?> $trait for SmartPtr<T> $($body)+
        }
    }
}

macro_rules! impl_mut_refs {
    (impl<T $(: $bound:path)?> $trait:ident for SmartPtr<T> $($body:tt)+) => {
        impl<T $(: $bound)?> $trait for &mut T $($body)+
        #[cfg(feature = "alloc")]
        impl<T $(: $bound)?> $trait for alloc::boxed::Box<T> $($body)+
    }
}

impl_refs! {
    impl<T: Len> Len for SmartPtr<T> {
        fn len(&self) -> usize {
            (**self).len()
        }
    }
}

impl<const N: usize, T> Collection for [T; N] {
    type Item = T;
}

impl_collection!([T]);

impl_refs! {
    impl<T: Collection> Collection for SmartPtr<T> {
        type Item = T::Item;
    }
}

impl_refs! {
    impl<T: First> First for SmartPtr<T> {
        fn first(&self) -> Option<&Self::Item> {
            (**self).first()
        }
    }
}

impl_mut_refs! {
    impl<T: FirstMut> FirstMut for SmartPtr<T> {
        fn first_mut(&mut self) -> Option<&mut Self::Item> {
            (**self).first_mut()
        }
    }
}

impl_refs! {
    impl<T: Last> Last for SmartPtr<T> {
        fn last(&self) -> Option<&Self::Item> {
            (**self).last()
        }
    }
}

impl_mut_refs! {
    impl<T: LastMut> LastMut for SmartPtr<T> {
        fn last_mut(&mut self) -> Option<&mut Self::Item> {
            (**self).last_mut()
        }
    }
}

delegate_first_and_co!(<T, const N> [T; N]);
delegate_first_and_co!(<T> [T]);

impl_mut_refs! {
    impl<T: PopLast> PopLast for SmartPtr<T> {
        fn pop_last(&mut self) -> Option<Self::Item> {
            (**self).pop_last()
        }
    }
}

impl_mut_refs! {
    impl<T: PopFirst> PopFirst for SmartPtr<T> {
        fn pop_first(&mut self) -> Option<Self::Item> {
            (**self).pop_first()
        }
    }
}

impl<T: core::str::FromStr + Len> core::str::FromStr for NonEmpty<T> {
    type Err = error::CollectionError<T::Err>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = s.parse::<T>().map_err(error::CollectionError::Other)?;
        NonEmpty::new(value).ok_or(error::CollectionError::Empty)
    }
}

#[cfg(feature = "serde")]
impl<T: serde::Serialize> serde::Serialize for NonEmpty<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_inner().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: serde::Deserialize<'de> + Len> serde::Deserialize<'de> for NonEmpty<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::Error;

        let collection = T::deserialize(deserializer)?;
        NonEmpty::new(collection).ok_or_else(|| D::Error::invalid_length(0, &"length greater than zero"))
    }
}

#[cfg(feature = "parse_arg")]
impl<T: parse_arg::ParseArg + Len> parse_arg::ParseArg for NonEmpty<T> {
    type Error = error::CollectionError<T::Error>;

    fn describe_type<W: fmt::Write>(mut writer: W) -> fmt::Result {
        T::describe_type(&mut writer)?;
        write!(writer, ", which is not empty")
    }

    fn parse_arg(arg: &std::ffi::OsStr) -> Result<Self, Self::Error> {
        let arg = T::parse_arg(arg).map_err(error::CollectionError::Other)?;
        NonEmpty::new(arg).ok_or(error::CollectionError::Empty)
    }

    fn parse_owned_arg(arg: std::ffi::OsString) -> Result<Self, Self::Error> {
        let arg = T::parse_owned_arg(arg).map_err(error::CollectionError::Other)?;
        NonEmpty::new(arg).ok_or(error::CollectionError::Empty)
    }
}

/// Represents collections that satisfy certain requirements.
///
/// All `std` collections are assumed to satisfy the requirements. In short, the requirements are
/// "the items don't magically vanish from collections/iterators, including via interior
/// mutability".
///
/// The list of requirements that need to be satisfied is not yet finalized so this trait has to
/// stay private - if it wasn't, adding a new requirement would be a breaking change with undefined
/// behavior implications - we definitely don't want that!
///
/// If you want this for your custom collection open an issue and we will see what can be done.
///
/// The current list of requirements:
///
/// * The number of elements in the collection MUST NOT be modifiable using a shared reference
/// * If a method on the collection says it adds an element to the collection it must actually do so,
///   this includes the `Extend` implementation
/// * If a method says it removes certain elements it MUST NOT remove any other elements even in case of
///   panic.
/// * If a method implements `First`, `FirstMut`, `Last`, `LastMut`, `PopFirst`, `PopLast` then each
///   of their methods MUST NOT return `None` if the collection is *not* empty, IOW, they may only
///   return `None` if the collection is empty.
/// * Once an element was added into a collection it MUST NOT disappear in any other way than calling
///   a method that says it removes that element and takes `&mut self`
/// * If the collection implements `IntoIterator` or its reference does the returned iterator MUST
///   return all elements in the collection (in an order specific for the collection)
/// * If the collection implements `Deref` then the `Target` is a borrowed representation of the
///   collection with same items. So if `T` is not empty then `T::Target` is not empty. Same for
///   `DerefMut`.
#[cfg_attr(not(non_empty_no_paranoid_checks), allow(unused))]
unsafe trait WellBehavedCollection {}

unsafe impl<const N: usize, T> WellBehavedCollection for [T; N] {}

unsafe impl<T> WellBehavedCollection for [T] {}

unsafe impl<T: WellBehavedCollection> WellBehavedCollection for NonEmpty<T> {}

unsafe fn unwrap_opt<Collection: ?Sized, T>(value: Option<T>) -> T {
    #[cfg(not(non_empty_no_paranoid_checks))]
    {
        value.unwrap()
    }
    #[cfg(non_empty_no_paranoid_checks)]
    {
        if is_well_behaved::<Collection>() {
            value.unwrap_unchecked()
        } else {
            value.unwrap()
        }
    }
}

/// Returns `true` if `T` implements `WellBehavedCollection`.
fn is_well_behaved<T>() -> bool {
    use core::cell::Cell;
    use core::marker::PhantomData;
    struct MaybeCopy<'a, U: ?Sized>(&'a Cell<bool>, PhantomData<U>);
    impl<'a, U: ?Sized> Clone for MaybeCopy<'a, U> {
        fn clone(&self) -> Self {
            self.0.set(false);
            MaybeCopy(self.0, self.1)
        }
    }
    impl<'a, U: WellBehavedCollection + ?Sized> Copy for MaybeCopy<'a, U> {}
    let is_well_behaved = Cell::new(true);
    let array = [MaybeCopy(&is_well_behaved, PhantomData::<T>)];
    let _ = array.clone();
    is_well_behaved.get()
}

struct IsNonZero<const N: usize>;
impl<const N: usize> IsNonZero<N> {
    const CHECK: () = { assert!(N != 0) };
}

#[cfg(test)]
mod tests {
}
