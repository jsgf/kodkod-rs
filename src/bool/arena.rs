//! Arena allocator for formula value storage
//!
//! Provides a wrapper around bumpalo::Bump for allocating temporary data structures
//! during formula translation. All allocations are freed when the arena is dropped.

use bumpalo::Bump;

/// Arena allocator for formula value allocation
///
/// Abstracts away bumpalo::Bump implementation details and provides a focused
/// API for allocating temporary data structures during formula translation.
/// All allocations are automatically freed when the arena is dropped.
pub struct MatrixArena {
    bump: Bump,
}

impl MatrixArena {
    /// Creates a new arena allocator
    pub fn new() -> Self {
        Self {
            bump: Bump::new(),
        }
    }

    /// Allocates a value in the arena and returns a reference to it
    pub fn alloc<T>(&self, value: T) -> &T {
        self.bump.alloc(value)
    }

    /// Allocates space for a slice and initializes it from an iterator
    pub fn alloc_slice_fill_iter<T, I>(&self, iter: I) -> &[T]
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        self.bump.alloc_slice_fill_iter(iter)
    }

    /// Allocates a value and returns a handle to it
    pub(crate) fn alloc_handle<T>(&self, value: T) -> super::Handle<T> {
        let boxed = self.bump.alloc(value);
        unsafe { super::Handle::new(boxed as *const T) }
    }

    /// Allocates a slice and returns a handle to it
    pub(crate) fn alloc_slice_handle<T>(&self, slice: &[T]) -> super::Handle<[T]>
    where
        T: Clone,
    {
        let allocated = self.alloc_slice_fill_iter(slice.iter().cloned());
        // Convert &[T] to raw pointer for Handle<[T]>
        unsafe { super::Handle::new(allocated as *const [T]) }
    }

    /// Resolves a handle to a reference with this arena's lifetime
    pub(crate) fn resolve_handle<'a, T: ?Sized>(&'a self, handle: super::Handle<T>) -> &'a T {
        unsafe { &*handle.ptr }
    }
}

impl Default for MatrixArena {
    fn default() -> Self {
        Self::new()
    }
}



