use std::collections::{HashMap, HashSet};
use std::vec::Vec;

use super::{NonEmpty, WellBehavedCollection};

unsafe impl<T> WellBehavedCollection for HashSet<T> {}
unsafe impl<K, V> WellBehavedCollection for HashMap<K, V> {}

super::impl_collection!(HashSet<T>);

impl<K, V> crate::Collection for HashMap<K, V> {
    type Item = V;
}

impl<K, V> crate::Len for HashMap<K, V> {
    fn len(&self) -> usize {
        self.len()
    }
}

// SOUNDNESS: &mut Path cannot change the length, only create a new, shorter reference which is fine
// since it doesn't update the original. We specifially do NOT implement this for references
// because then the change would become possible.
unsafe impl crate::traits::FixedLenCollection for std::path::Path {}
// SOUNDNESS: &mut OsStr cannot change the length, only create a new, shorter reference which is
// fine since it doesn't update the original. We specifially do NOT implement this for references
// because then the change would become possible.
unsafe impl crate::traits::FixedLenCollection for std::ffi::OsStr {}

impl std::io::Write for NonEmpty<Vec<u8>> {
    #[inline]
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        unsafe { self.inner_mut().write(bytes) }
    }

    #[inline]
    fn write_all(&mut self, bytes: &[u8]) -> std::io::Result<()> {
        unsafe { self.inner_mut().write_all(bytes) }
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        unsafe { self.inner_mut().write_vectored(bufs) }
    }

    #[inline]
    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        unsafe { self.inner_mut().write_fmt(args) }
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        unsafe { self.inner_mut().flush() }
    }
}

impl std::io::Write for crate::vec::NonEmptyVec<u8> {
    #[inline]
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.with_vec(move |vec| vec.write(bytes))
    }

    #[inline]
    fn write_all(&mut self, bytes: &[u8]) -> std::io::Result<()> {
        self.with_vec(move |vec| vec.write_all(bytes))
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        self.with_vec(move |vec| vec.write_vectored(bufs))
    }

    #[inline]
    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        self.with_vec(move |vec| vec.write_fmt(args))
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        self.with_vec(move |vec| vec.flush())
    }
}
