//! Contains the error types.
//!
//! The most prominent type is `EmptyCollectionError`, which is used in `TryFrom` implementations.

use core::fmt;
#[cfg(feature = "std")]
pub use std::error::Error as StdError;
#[cfg(all(not(feature = "std"), feature = "newer-rust"))]
if_rust_version::if_rust_version! {
    >= 1.81 {
        pub use core::error::Error as StdError;
    }
}

macro_rules! if_std_error {
    ($($t:tt)*) => {
        #[cfg(feature = "std")]
        #[cfg_attr(docsrs, doc(cfg(any(feature = "std", all(feature = "newer-rust", rust_version = ">= 1.81")))))]
        $($t)*
        #[cfg(all(not(feature = "std"), feature = "newer-rust"))]
        if_rust_version::if_rust_version! {
            >= 1.81 {
                #[cfg_attr(docsrs, doc(cfg(any(feature = "std", all(feature = "newer-rust", rust_version = ">= 1.81")))))]
                $($t)*
            }
        }
    };
}
pub(crate) use if_std_error;

/// Returned when a collection that shouldn't be empty is empty.
///
/// This is used mainly in `TryFrom` implementations.
#[derive(Debug)]
#[non_exhaustive]
pub struct EmptyCollectionError;

impl fmt::Display for EmptyCollectionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "the collection is empty")
    }
}

if_std_error! {
    impl StdError for EmptyCollectionError {}
}

/// An error returned when constructing a collection failed.
///
/// This is used to wrap other fallible constructions to extend the error type with the `Empty`
/// variant. For instance, the `FromStr` impl will return `Empty` if the collection was empty but
/// otherwise valid or `Other` if parsing failed for a different reason (such as invalid
/// characters).
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum CollectionError<E> {
    /// The collection failed to construct for other reason than being empty.
    ///
    /// Note that this doesn't guarantee that the collection *also* isn't empty. In theory, it's
    /// possible that the collection is empty and invalid for other reason at the same time though
    /// I can't find a real-world example because empty collections are usually valid.
    Other(E),

    /// The collection failed to construct because it's empty (but valid otherwise).
    ///
    /// If this variant is returned the collection was valid but empty. A common example is parsing
    /// an empty string which is trivially valid but if non-empty one was requested this error has
    /// to be returned.
    Empty,
}

impl<E: fmt::Display> fmt::Display for CollectionError<E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CollectionError::Other(error) => fmt::Display::fmt(error, f),
            CollectionError::Empty => write!(f, "the value is empty"),
        }
    }
}

if_std_error! {
    impl<E: StdError> StdError for CollectionError<E> {
        #[inline]
        fn source(&self) -> Option<&(dyn StdError + 'static)> {
            match self {
                CollectionError::Other(error) => error.source(),
                CollectionError::Empty => None,
            }
        }
    }
}
