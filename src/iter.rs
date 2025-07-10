//! Non-empty iterator interface
//!
//! This module contains a trait [`NonEmptyIntoIter`] similar to [`IntoIterator`] and [`Iterator`]
//! which guarantees the resulting iterator is not empty. There's one significant difference: while
//! the usual iterators work by first converting a collection into an iterator and then applying
//! combinators, this has to work the other way around - first apply the combinators and then
//! convert into iterator. This is because the iterator is only non-empty at the beginning of
//! iteration. Thus the conversion inevitably performs the first step of iteration as well. Doing
//! this obviously changes the type, hence the conversion.
//!
//! A similar approach had to be taken in case of `DoubleEndedIterator` equivalent - that one
//! allows to start with the last item.
//!
//! The module also contains [`FromNonEmptyIterator`] trait which is similar to `FromIterator`
//! except it restricts the iterator to be non-empty. As a result non-empty collections can (and
//! do) implement this trait to get an infallible constructor. This enables infallibly transforming
//! a non-empty collection into another non-empty collection.

use core::cmp::Ordering;
use crate::WellBehavedCollection;

/// Represents types that can be converted into an iterator that guarantees to return at least one
/// item.
pub trait NonEmptyIntoIter: IntoIterator + Sized {
    /// Splits the collection into first element and an iterator of remaining elements.
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter);

    /// Applies function or closure `f` to each item.
    ///
    /// Importantly this doesn't change the number of iterated items so the resulting iterator is
    /// still non-empty.
    fn map<U, F>(self, f: F) -> Map<Self, F> where F: FnMut(Self::Item) -> U {
        Map {
            iter: self,
            f,
        }
    }

    /// Repeatedly applies the closure to pair of items.
    ///
    /// The return value is used as an accumulator and always passed as the left parameter on next
    /// iteration.
    ///
    /// This is practically the same as [`Iterator::reduce`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn reduce<F>(self, f: F) -> Self::Item where F: FnMut(Self::Item, Self::Item) -> Self::Item {
        let (accum, iter) = self.into_first_and_remaining();
        iter.fold(accum, f)
    }

    /// Finds the minimum value in the iterator according to the `Ord` impl.
    ///
    /// This is practically the same as [`Iterator::min`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn min(self) -> Self::Item where Self::Item: Ord {
        self.reduce(Ord::min)
    }

    /// Finds the minimum value in the iterator according to the provided closure.
    ///
    /// This is practically the same as [`Iterator::min_by`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn min_by<F>(self, mut f: F) -> Self::Item where F: FnMut(&Self::Item, &Self::Item) -> Ordering {
        self.reduce(move |a, b| if f(&a, &b).is_le() { a } else { b })
    }

    /// Finds the minimum value in the iterator according to the `Ord` impl on the key computed by
    /// the closure.
    ///
    /// This is practically the same as [`Iterator::min_by_key`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn min_by_key<K, F>(self, mut f: F) -> Self::Item where F: FnMut(&Self::Item) -> Ordering {
        self.reduce(move |a, b| if f(&a) <= f(&b) { a } else { b })
    }

    /// Finds the minimum value in the iterator according to the `Ord` impl.
    ///
    /// This is practically the same as [`Iterator::max`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn max(self) -> Self::Item where Self::Item: Ord {
        self.reduce(Ord::max)
    }

    /// Finds the maximum value in the iterator according to the provided closure.
    ///
    /// This is practically the same as [`Iterator::max_by`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn max_by<F>(self, mut f: F) -> Self::Item where F: FnMut(&Self::Item, &Self::Item) -> Ordering {
        self.reduce(move |a, b| if f(&a, &b).is_ge() { a } else { b })
    }

    /// Finds the maximum value in the iterator according to the `Ord` impl on the key computed by
    /// the closure.
    ///
    /// This is practically the same as [`Iterator::max_by_key`] except it doesn't return [`Option`]
    /// because of the non-empty guarantee.
    fn max_by_key<K, F>(self, mut f: F) -> Self::Item where F: FnMut(&Self::Item) -> Ordering {
        self.reduce(move |a, b| if f(&a) >= f(&b) { a } else { b })
    }

    /// Creates collection.
    ///
    /// This is practically the same as [`Iterator::collect`] except it allows creating non-empty
    /// types taking advantage of the fact that the iterator is not empty.
    fn collect<T>(self) -> T where T: FromNonEmptyIterator<Self::Item> {
        T::from_non_empty_iter(self)
    }
}

/// Creates collection from a non-empty iterator.
///
/// This is generally implemented for collections that are guaranteed to be non-empty.
pub trait FromNonEmptyIterator<Item> {
    /// Creates the collection.
    fn from_non_empty_iter<I: NonEmptyIntoIter<Item = Item>>(iter: I) -> Self;
}

/* Curiously, this is not allowed even though in principle it should.
impl<Item, T: FromIterator<Item>> FromNonEmptyIterator<Item> for T {
    fn from_non_empty_iter<I: IntoIterator<Item = Item>>(iter: I) -> Self {
        iter.into_iter().collect()
    }
}
*/

pub(crate) fn from_iter_spec<S: NonEmptyIntoIter, D: crate::traits::FromInner>(src: S) -> D where D::Inner: FromIterator<S::Item> {
    let collection = if crate::is_well_behaved::<S>() {
        src.into_iter().collect()
    } else {
        let (first, iter) = src.into_first_and_remaining();
        core::iter::once(first).chain(iter).collect()
    };
    unsafe { D::from_inner(collection) }
}

/// A combinator returned from [`NonEmptyIntoIter::map`].
///
/// See the method for more details.
pub struct Map<Iter, F> {
    iter: Iter,
    f: F,
}

impl<Iter: NonEmptyIntoIter, U, F: FnMut(Iter::Item) -> U> IntoIterator for Map<Iter, F> {
    type IntoIter = core::iter::Map<Iter::IntoIter, F>;
    type Item = U;

    fn into_iter(self) -> Self::IntoIter {
        self.iter.into_iter().map(self.f)
    }
}

impl<Iter: NonEmptyIntoIter, U, F: FnMut(Iter::Item) -> U> NonEmptyIntoIter for Map<Iter, F> {
    fn into_first_and_remaining(mut self) -> (Self::Item, Self::IntoIter) {
        let (first, remaining) = self.iter.into_first_and_remaining();
        let first = (self.f)(first);
        let iter = remaining.map(self.f);
        (first, iter)
    }
}

unsafe impl<Iter: WellBehavedCollection, F> WellBehavedCollection for Map<Iter, F> {}

/// Provides the implementation of the `into_first_and_remaining` method.
///
/// # Soundness
///
/// May only be called on a non-empty collection.
pub(crate) unsafe fn into_first_and_remaining<T: IntoIterator>(iter: T) -> (T::Item, T::IntoIter) {
    let mut iter = iter.into_iter();
    let first = crate::unwrap_opt::<T, _>(iter.next());
    (first, iter)
}

/// Represents types that can be converted into a double-ended iterator that guarantees to return
/// at least one item.
pub trait DoubleEndedNonEmptyIntoIter: NonEmptyIntoIter where Self::IntoIter: DoubleEndedIterator {
    /// Splits the collection into last element and an iterator of remaining elements.
    fn into_last_and_remaining(self) -> (Self::Item, Self::IntoIter);

    /// Reverses the direction of the iterator.
    fn rev(self) -> Rev<Self> {
        Rev(self)
    }
}

/// A combinator returned from [`DoubleEndedNonEmptyIntoIter::rev`].
///
/// See the method for more details.
pub struct Rev<T>(T);

impl<T: IntoIterator> IntoIterator for Rev<T> where T::IntoIter: DoubleEndedIterator {
    type Item = T::Item;
    type IntoIter = core::iter::Rev<T::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().rev()
    }
}

impl<T: DoubleEndedNonEmptyIntoIter> NonEmptyIntoIter for Rev<T> where T::IntoIter: DoubleEndedIterator {
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        let (first, remaining) = self.0.into_last_and_remaining();
        (first, remaining.rev())
    }
}

impl<T: DoubleEndedNonEmptyIntoIter> DoubleEndedNonEmptyIntoIter for Rev<T> where T::IntoIter: DoubleEndedIterator {
    fn into_last_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        let (first, remaining) = self.0.into_first_and_remaining();
        (first, remaining.rev())
    }
}

/// An iterator producing exactly one element and guaranteeing non-emptyness.
///
/// See the method for more details.
pub struct Once<T>(T);

impl<T> IntoIterator for Once<T> {
    type Item = T;
    type IntoIter = core::iter::Once<T>;

    fn into_iter(self) -> Self::IntoIter {
        core::iter::once(self.0)
    }
}

impl<T> NonEmptyIntoIter for Once<T> {
    fn into_first_and_remaining(self) -> (Self::Item, Self::IntoIter) {
        let mut iter = self.into_iter();
        let first = iter.next().unwrap();

        (first, iter)
    }
}
