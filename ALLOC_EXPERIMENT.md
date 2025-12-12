# Allocation Experiment

Currently we have two different allocation schemes present:
- An arena allocator, where allocations are represented by Handle types
with lifetimes tied to the arena. This has very fast allocation, bulk
deallocation, and Handle can be copy so they can be shared freely without
.clone() or similar. The downside is that we have 'arena lifetimes all over
the place, and managing them can be awkward.
- Reference counting with Rc<T>. This is more "normal" Rust memory management
which avoids most of the lifetime management problems. The downsides are
more use of .clone() to bump reference counts, per-object alloc/free cost,
and per-object refcount overhead.

Neither is particularly multithread-safe, though Rc could convert to Arc,
and add Mutex to replace RefCell. We could probably do something with arena
allocator too (at least with scoped threads). That's secondary though.

The goal of the experiment is to:
- See if we can unify on one model or the other entirely
- Is there a perf impact for one approach over the other
- What does the effect on the user API look like

## Performing the experiment

Starting from the current git repo, we'll create two separate branches:
- arenaalloc
- refcount

Leave the `master` branch untouched.

Within each branch, convert the code to *completely* use one approach or the other.
Nothing is off limits - make as sweeping changes to the API as needed to support the
allocation approach.

Since one of the goals is to see the effect on the user API, *all* examples and tests
should be changed appropriately, using the most idiomatic approach afforded by the
allocation scheme.

### Arena allocation notes

- We can have multiple arenas, but the basic arena slab allocator and
Handle implementation must be shared.
- Neither the arena or handle objects should be directly exposed in the
public API; they should always be in a suitable wrapper.
- The arena API works best when the arena is owned by some central object
which is a natural part of the API anyway (eg some kind of factory-like object)
- The public API *MUST* be *COMPLETELY* safe according to Rust's safety rules.
There must be *ABSOLUTELY NO VIOLATIONS* of memory safety. Do not expose `'static`
lifetimes, even if they're needed internally. 
- Raw pointers must *never* be used as the key in a map or set
structure. Turning it into a usize *may* be OK, so long as there's a
*STRONG* guarantee that it won't outlive the arena its allocated from.


### Refcount notes

- Try to avoid too many .clone() calls.

# Keeping track

Keep track of state here:

## Refcount Branch

### Progress
- [x] Branch created
- [x] Core boolean layer converted (src/bool.rs, src/bool/factory.rs, src/bool/int.rs)
- [x] Arena infrastructure removed (src/bool/arena.rs deleted)
- [x] Boolean layer validated with cargo check
- [x] Translator layer converted
- [x] CNF and engine layers converted
- [x] Library compilation validated
- [ ] Tests updated (0/24)
- [ ] Examples updated (0/60)
- [ ] Full test suite passing
- [ ] Performance analysis complete

### Notes

#### Conversion Completed
- Removed all lifetime parameters from boolean layer types
- Replaced `Handle<'arena, T>` with `Rc<T>` and `Rc<[T]>` for slices
- Removed MatrixArena entirely
- Updated FormulaKind to use Rc for storing child references
- Removed unsafe lifetime transmutation from factory cache
- BooleanFormula is now Clone (not Copy) due to Rc fields
- All public APIs now free of arena-related lifetimes

#### Key Changes
- src/bool.rs: Removed Handle type, updated BoolValue/BooleanFormula/BooleanMatrix to remove lifetimes
- src/bool/factory.rs: Removed arena field, updated cache to use BooleanFormula directly (no 'static hack)
- src/bool/int.rs: Removed lifetime parameter from Int
- src/cnf.rs: Removed arena dependency, access Rc directly
- All translator files: Removed lifetime parameters

#### Next Steps
- Update all test files to remove lifetime parameters
- Update all example files to remove lifetime parameters
- Run full test suite and fix any failures
- Measure performance impact

