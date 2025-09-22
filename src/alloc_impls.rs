use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::collections::{BTreeSet, BTreeMap, VecDeque};
use alloc::rc::Rc;
#[cfg(target_has_atomic = "ptr")]
use alloc::sync::Arc;
use alloc::string::String;

use super::WellBehavedCollection;
use super::NonEmpty;

super::impl_collection!(Vec<T>, BTreeSet<T>, VecDeque<T>);
super::delegate_first_and_co!(<T> Vec<T>);
#[cfg(feature = "newer-rust")]
if_rust_version::if_rust_version! {
    >= 1.66 {
        super::delegate_first_shared_and_co!(<T: Ord> BTreeSet<T>);
    }
}
super::delegate_first_and_co!(<T> VecDeque<T>);

impl crate::Collection for String {
    type Item = char;
}

impl crate::Len for String {
    fn len(&self) -> usize {
        self.len()
    }
}

unsafe impl<T: WellBehavedCollection + ?Sized> WellBehavedCollection for Box<T> {}
unsafe impl<T: WellBehavedCollection + ?Sized> WellBehavedCollection for Rc<T> {}
#[cfg(target_has_atomic = "ptr")]
unsafe impl<T: WellBehavedCollection + ?Sized> WellBehavedCollection for Arc<T> {}

unsafe impl<T> WellBehavedCollection for Vec<T> {}
unsafe impl<T> WellBehavedCollection for BTreeSet<T> {}
unsafe impl<T> WellBehavedCollection for VecDeque<T> {}

unsafe impl<K, V> WellBehavedCollection for BTreeMap<K, V> {}

macro_rules! impl_reserve {
    ($($ty:ident$(<$gen:ident>)?),*) => {
        $(
            impl$(<$gen>)? super::Reserve for $ty$(<$gen>)? {
                fn reserve(&mut self, capacity: usize) {
                    self.reserve(capacity);
                }
            }
        )*
    }
}
pub(crate) use impl_reserve;

impl_reserve!(Vec<T>, VecDeque<T>, String);

impl<K, V> crate::Collection for BTreeMap<K, V> {
    type Item = V;
}

impl<K, V> crate::Len for BTreeMap<K, V> {
    fn len(&self) -> usize {
        self.len()
    }
}

impl<K: Ord, V> crate::First for BTreeMap<K, V> {
    fn first(&self) -> Option<&Self::Item> {
        self.values().next()
    }
}

impl<K: Ord, V> crate::FirstMut for BTreeMap<K, V> {
    fn first_mut(&mut self) -> Option<&mut Self::Item> {
        self.values_mut().next()
    }
}

impl<K: Ord, V> crate::Last for BTreeMap<K, V> {
    fn last(&self) -> Option<&Self::Item> {
        self.values().next_back()
    }
}

impl<K: Ord, V> crate::LastMut for BTreeMap<K, V> {
    fn last_mut(&mut self) -> Option<&mut Self::Item> {
        self.values_mut().next_back()
    }
}

impl<K: Ord, V> crate::NonEmpty<BTreeMap<K, V>> {
    /// Returns shared references to the first key and value.
    pub fn first_key_value(&self) -> (&K, &V) {
        // SAFETY: `T` is the collection we are storing and we are non-empty.
        unsafe { crate::unwrap_opt::<BTreeMap<K, V>, _>(self.as_inner().iter().next()) }
    }

    /// Returns a shared reference to the first key and a mutable reference to the first value.
    pub fn first_key_value_mut(&mut self) -> (&K, &mut V) {
        // SAFETY: `T` is the collection we are storing and we are non-empty.
        unsafe { crate::unwrap_opt::<BTreeMap<K, V>, _>(self.inner_mut().iter_mut().next()) }
    }

    #[cfg(feature = "newer-rust")]
    if_rust_version::if_rust_version! {
        >= 1.66 {
            /// Attempts to remove the first key-value pair.
            ///
            /// Returns `None` if the map would become empty after removal.
            pub fn try_pop_first_key_value(&mut self) -> Option<(K, V)> {
                if self.as_inner().len() >= 2 {
                    // SAFETY: we've checked that the length is large enough to not leave `self` empty
                    unsafe { self.inner_mut().pop_first() }
                } else {
                    None
                }
            }
        }
    }

    /// Returns shared references to the last key and value.
    pub fn last_key_value(&self) -> (&K, &V) {
        // SAFETY: `T` is the collection we are storing and we are non-empty.
        unsafe { crate::unwrap_opt::<BTreeMap<K, V>, _>(self.as_inner().iter().next_back()) }
    }

    /// Returns a shared reference to the last key and a mutable reference to the last value.
    pub fn last_key_value_mut(&mut self) -> (&K, &mut V) {
        // SAFETY: `T` is the collection we are storing and we are non-empty.
        unsafe { crate::unwrap_opt::<BTreeMap<K, V>, _>(self.inner_mut().iter_mut().next_back()) }
    }

    #[cfg(feature = "newer-rust")]
    if_rust_version::if_rust_version! {
        >= 1.66 {
            /// Attempts to remove the last key-value pair.
            ///
            /// Returns `None` if the map would become empty after removal.
            pub fn try_pop_last_key_value(&mut self) -> Option<(K, V)> {
                if self.as_inner().len() >= 2 {
                    // SAFETY: we've checked that the length is large enough to not leave `self` empty
                    unsafe { self.inner_mut().pop_last() }
                } else {
                    None
                }
            }
        }
    }
}

impl<T> crate::PopFirst for Vec<T> {
    fn pop_first(&mut self) -> Option<Self::Item> {
        if self.is_empty() {
            None
        } else {
            Some(self.remove(0))
        }
    }
}

impl<T> crate::PopLast for Vec<T> {
    fn pop_last(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}

#[cfg(feature = "newer-rust")]
if_rust_version::if_rust_version! {
    >= 1.66 {
        impl<T: Ord> crate::PopFirst for BTreeSet<T> {
            fn pop_first(&mut self) -> Option<Self::Item> {
                self.pop_first()
            }
        }

        impl<T: Ord> crate::PopLast for BTreeSet<T> {
            fn pop_last(&mut self) -> Option<Self::Item> {
                self.pop_last()
            }
        }

        impl<K: Ord, V> crate::PopFirst for BTreeMap<K, V> {
            fn pop_first(&mut self) -> Option<Self::Item> {
                self.pop_first().map(|value| value.1)
            }
        }

        impl<K: Ord, V> crate::PopLast for BTreeMap<K, V> {
            fn pop_last(&mut self) -> Option<Self::Item> {
                self.pop_last().map(|value| value.1)
            }
        }
    }
}

impl<T> crate::PopFirst for VecDeque<T> {
    fn pop_first(&mut self) -> Option<Self::Item> {
        self.pop_front()
    }
}

impl<T> crate::PopLast for VecDeque<T> {
    fn pop_last(&mut self) -> Option<Self::Item> {
        self.pop_back()
    }
}

impl crate::PopFirst for String {
    fn pop_first(&mut self) -> Option<Self::Item> {
        if self.is_empty() {
            None
        } else {
            Some(self.remove(0))
        }
    }
}

impl crate::PopLast for String {
    fn pop_last(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}

// SOUNDNESS: the length is defined by the type and that cannot change during run time even for
// references.
unsafe impl<const N: usize, T> crate::traits::FixedLenCollection for Box<[T; N]> {}
// SOUNDNESS: the length is defined by the type and that cannot change during run time even for
// references.
unsafe impl<const N: usize, T> crate::traits::FixedLenCollection for Rc<[T; N]> {}
// SOUNDNESS: the length is defined by the type and that cannot change during run time even for
// references.
#[cfg(target_has_atomic = "ptr")]
unsafe impl<const N: usize, T> crate::traits::FixedLenCollection for Arc<[T; N]> {}

impl<K: Ord + core::borrow::Borrow<Q>, V, Q: Ord + ?Sized> core::ops::Index<&Q> for NonEmpty<alloc::collections::BTreeMap<K, V>> {
    type Output = V;

    fn index(&self, key: &Q) -> &Self::Output {
        &self.as_inner()[key]
    }
}
