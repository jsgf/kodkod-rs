//! Arena allocator for BooleanMatrix storage
//!
//! Provides a wrapper around bumpalo::Bump for allocating temporary data structures
//! during formula translation. All allocations are freed when the arena is dropped.

use bumpalo::Bump;

/// Arena allocator for matrix storage
///
/// Abstracts away bumpalo::Bump implementation details and provides a focused
/// API for allocating temporary data structures during formula translation.
/// All allocations are automatically freed when the arena is dropped.
///
/// # Example
/// ```ignore
/// let arena = MatrixArena::new();
/// let map = ahash::AHashMap::new();
/// // ... populate map ...
/// let shared_map = arena.alloc(map);  // allocate in arena
/// // shared_map is now &AHashMap with lifetime tied to arena
/// ```
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
    ///
    /// The returned reference has lifetime tied to the arena.
    /// The value is not moved out of the arena - the original value
    /// is consumed and the reference is returned.
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
}

impl Default for MatrixArena {
    fn default() -> Self {
        Self::new()
    }
}
