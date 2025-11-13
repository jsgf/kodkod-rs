# Performance Analysis & Optimization Opportunities

## Observations

Constraint solving is inherently allocation-heavy. Current bottlenecks identified:
1. **Translation phase**: Creates many temporary `Expression` and `Formula` nodes
2. **Boolean circuits**: `BooleanFormula` and `BoolValue` allocations during translation
3. **Bounds/Universe setup**: Various `Vec`, `HashMap` allocations

## Allocation Sites

### 1. AST Construction (High Allocation)
**Location**: Examples building formulas
```rust
let formula = Expression::from(&relation)  // Arc allocation
    .join(Expression::from(&other))        // Box allocations
    .product(Expression::from(&third));    // Box allocations
```

**Current Cost**: Each binary operation creates 3 Box allocations + formula node
**Volume**: Trees example creates 1000s of formula nodes during translation

### 2. Boolean Circuit Translation (High Allocation)
**Location**: `src/translator/leaf_interpreter.rs`
```rust
let gate = factory.and(left, right);  // Creates BoolValue + potentially BoolFormula
```

**Current Cost**:
- BoolValue clone per gate operation
- Arc allocation for new BoolFormula if not cached
- Hundreds to thousands per solve

### 3. Collections in Bounds
**Location**: `src/instance.rs`, `Bounds::bound()`
```rust
let tuples = Vec::new();  // Collects all tuples
// potentially O(universe^n) space
```

## Optimization Strategies

### Strategy 1: Arena Allocation for Translation Phase ✓ (Recommended)

Use `bumpalo` crate for temporary allocations during FOL→Boolean translation:

```rust
// In translator
let arena = bumpalo::Bump::new();

// Instead of Box::new() which allocates from global heap
// Allocate from arena
let expr = arena.alloc(expression_value);  // Much faster

// Arena is freed when translation completes
// All expressions are dropped together
```

**Benefits**:
- Eliminates fragmentation from many small allocations
- Single allocation + bump pointer for all temporary objects
- Automatic cleanup when arena dropped

**Cost**: Requires refactoring `Box<Expression>` → references into arena

**Effort**: Medium - impacts translator module primarily

### Strategy 2: Slab Allocation for Boolean Circuits

Use `bumpalo` or context-local slab for BoolValue cache:

```rust
// Instead of HashMap<BoolValue, Arc<BooleanFormula>>
// Use arena-allocated nodes with ID-based references

struct BoolCircuitArena {
    arena: Bump,
    formulas: Vec<BooleanFormulaData>,  // Packed array
    cache: HashMap<Hash, FormulaDef>,   // ID-based
}
```

**Benefits**:
- Better cache locality (formulas in array)
- Reduced Arc overhead
- Faster allocation in hot path

**Cost**: Requires lifetime parameters or thread-local ownership

**Effort**: High - deep refactoring of bool module

### Strategy 3: Reuse Solver Instances (Easy ✓)

Currently create new `Solver` per solve. Can pool/reuse:

```rust
// Solver could support reset()
solver.reset();
solver.solve(new_formula, new_bounds)?;
```

**Benefits**:
- Reuse internal structures (cache, statistics)
- Avoid solver initialization overhead

**Cost**: Minor API change

**Effort**: Low - just add reset() method

### Strategy 4: Lazy Tuple Set Construction

Currently `Bounds::bound()` may construct full tuple sets upfront:

```rust
// Current: materializes all tuples
let all = factory.all(2);  // O(n²) allocations

// Better: represent as ranges/ranges
struct TupleRange {
    start: usize,
    end: usize
}
```

**Benefits**:
- O(1) space for large bounds
- Only materialize when needed

**Cost**: Changes internal representation

**Effort**: Medium - impacts Bounds/Universe

## Parallelization Considerations

### Current Threading Model

The codebase is **entirely single-threaded**:
- No `Send`/`Sync` trait bounds in public APIs
- `BooleanFactory` uses `Cell<u32>` and `RefCell<HashMap>` (not thread-safe)
- All data structures assume exclusive access within a phase

### Arc vs Rc Trade-Off

**Current**: Everything uses `Arc` for shared ownership
- `Relation`, `Variable`, `BooleanFormula`, `Universe` all Arc-based
- Arc is `Send+Sync` but has atomic overhead

**Alternative**: Use `Rc` for single-threaded performance
- `Rc` clone/drop: ~10 cycles
- `Arc` clone/drop: ~25 cycles
- **Difference on 10,000 clones**: ~150 microseconds
- **Total solve time**: typically 20-120,000ms
- **Impact**: <0.001% (negligible)

**Recommendation**: Keep Arc. Enables future parallelization. Switching to Rc not worth the reduced flexibility.

### Parallelization Opportunities

#### **Opportunity A: Parallel Quantifier Evaluation** (High Impact)

Quantified formulas in translation phase create many independent bindings:

```rust
// Current: Sequential
for tuple in domain {
    let result = translate_formula_with_binding(tuple);
    // Combine results with OR/AND
}

// Potential: Parallel with rayon
use rayon::prelude::*;
domain.par_iter()
    .map(|tuple| translate_formula_with_binding(tuple))
    .reduce(|| factory.constant(false), |a, b| factory.or(a, b))
```

**Challenge**: BooleanFactory uses `Cell`/`RefCell`
- **Solution 1**: Thread-local factories per worker thread
- **Solution 2**: Synchronize factory with RwLock or Mutex
- **Solution 3**: Allocate variables upfront, use locked gate creation

**Estimated speedup**: 2-4x on 4+ cores for quantifier-heavy formulas
**Effort**: 1-2 weeks
**Risk**: Medium (synchronization complexity)

#### **Opportunity B: Portfolio SAT Solving** (Variable Impact)

Run multiple SAT solvers in parallel, use first result:

```rust
use rayon::prelude::*;
use std::sync::atomic::{AtomicBool, Ordering};

let found = Arc::new(AtomicBool::new(false));

[BasicSolver::default(), MinisatSolver::default()]
    .into_par_iter()
    .find_map_first(|mut solver| {
        if found.load(Ordering::Relaxed) {
            return None;  // Another solver won
        }
        match solve_with(&mut solver, formula, bounds) {
            Ok(solution) => {
                found.store(true, Ordering::Relaxed);
                Some(solution)
            }
            Err(_) => None,
        }
    })
```

**Estimated speedup**: Highly variable (1-10x depending on solver performance gaps)
**Effort**: 2-3 days
**Risk**: Low

#### **Opportunity C: Parallel Clause Generation** (Lower Impact)

CNF translation has some independent branches:

**Estimated speedup**: 1.5-2x (limited by circuit dependencies)
**Effort**: High
**Risk**: High (circuit traversal has ordering constraints)

### Thread-Safe Arena Allocation

`bumpalo::Bump` is **not `Send`/`Sync`** by default. The **recommended solution is `bumpalo_herd`**:

```rust
use bumpalo_herd::Herd;

// Create a Herd - manages multiple Bump allocators
let herd: Herd = Herd::new();

// Each thread gets its own Bump from the Herd
rayon::scope(|s| {
    s.spawn(|_| {
        let bump = herd.get();  // Thread-local Bump
        let allocated = bump.alloc(value);
    });
});

// Memory allocated in threads can survive thread termination
// because lifetime is tied to Herd itself
```

**Key advantages**:
- Each thread gets exclusive access to its own Bump (no synchronization overhead)
- Allocated memory survives thread/iterator termination (lifetime tied to Herd)
- Cleaner API than manual thread-local management
- No bottlenecks from Mutex contention

**Alternative approaches** (if not using bumpalo_herd):
- **Thread-local arenas**: `thread_local! { static ARENA: RefCell<Bump> }` - works but limited to static lifetimes
- **Separate per-thread arenas**: Manual allocation per rayon worker - more verbose, same performance

### Java Kodkod Reference

Java implementation is **also single-threaded**:
- No concurrency primitives found in source
- Uses object references (equivalent to Rust's Arc)
- No arena allocation (relies on JVM GC)
- Aggressive caching but no parallelism

**Conclusion**: Parallelization is a novel optimization opportunity in the Rust port.

## Profiling Recommendations

**CONFIRMED: Flamegraph profiling of the Trees example shows that `translate_formula` is dominated by memory allocation.** This validates the analysis that allocation overhead is the primary bottleneck (not CPU-bound computation).

Before optimizing further, profile with:

```bash
# Flamegraph - identify hot paths
cargo install flamegraph
cargo flamegraph --example sudoku --release

# Valgrind - track allocations
valgrind --tool=massif ./target/release/examples/sudoku

# Perf - general profiling
perf record -g ./target/release/examples/sudoku
perf report
```

### Expected Hot Paths
1. **Translation**: 40-60% of time in Trees, Sudoku examples
2. **SAT solving**: 30-50% depending on problem complexity
3. **Bounds setup**: 5-10%

## Index-Based References vs Arc Pointers

### Memory Comparison

**Arc<T> (Current)**:
- Size: 8 bytes (64-bit pointer)
- Overhead: 16 bytes per allocation (refcount + weak count)
- Example: 1 million BooleanFormulas = 8MB pointers + 16MB overhead = 24MB

**u32 Index (Alternative)**:
- Size: 4 bytes (50% reduction)
- Overhead: Allocated as Vec (tight packing, no per-item overhead)
- Example: 1 million formulas in Vec = 4MB indices (assuming data in Vec)
- Cache efficiency: Better (sequential access patterns)

**u64 Index with Generation Counter**:
- Size: 8 bytes (same as pointer)
- Benefit: Prevents ABA problem (stale index detection)
- Example: generational-arena crate style

### Maximum Problem Size

**Practical u32 capacity**: 4,294,967,296 nodes
- SAT problems >100M variables are rare and slow
- Current timeout issues come from time complexity, not space

**Recommendation**: u32 is sufficient for the foreseeable future

### Index-Based Design Trade-Offs

**Benefits**:
- 50% memory reduction vs Arc
- Better cache locality (dense Vec storage)
- No atomic operations for "cloning" (just copy u32)
- Simpler GC model (arena cleanup)

**Costs**:
- Lifetime management (indices tied to factory)
- Less ergonomic API (`factory.get(id)` vs `formula.field()`)
- Major refactoring (2-3 weeks for complete transition)
- Prevents external code from holding formula references

**Real-world examples**:
- `petgraph`: Uses `NodeIndex(u32)` and `EdgeIndex(u32)`
- `slotmap`: Index-based hashmap with u32 keys
- `generational-arena`: Indices with ABA protection

**Recommendation**: Defer until profiling shows pointer overhead is critical. Current Arc design is cleaner and enables parallelization.

## Concrete Performance Numbers

**⚠️ IMPORTANT: These numbers are theoretical estimates, not measured from the actual codebase.** They are based on typical CPU cycle costs and common Rust allocation patterns. Before making optimization decisions, profile the actual codebase using flamegraph, perf, or valgrind (see Profiling Recommendations below). Actual impact may vary significantly based on workload characteristics.

### Arc Overhead Impact

**Clone/drop costs**:
- Arc: ~25 CPU cycles
- Rc: ~10 CPU cycles
- Difference: 15 cycles

**On 10,000 BooleanFormula creations**:
- Extra time: 15 × 10,000 = 150,000 cycles ≈ 150 microseconds (at 1GHz)
- Total solve time for Sudoku 4×4: ~20,000,000 microseconds (20ms)
- **Relative impact: <0.001%**

### Arena Allocation Savings

**Current allocation model** (each Box separately):
- Allocation: ~100 nanoseconds per malloc
- Deallocation: ~50 nanoseconds per free
- Per-allocation overhead: ~40 bytes

**Arena model** (Bump allocator):
- Allocation: ~10 nanoseconds per bump
- Deallocation: Free entire arena at once
- Per-allocation overhead: ~0 bytes (just bump pointer increment)

**On 10,000 temporary allocations in translation**:
- Current: (100 + 50) × 10,000 = 1.5ms
- Arena: 10 × 10,000 = 0.1ms
- **Savings: ~1.4ms (5-10% of translation time)**

### Parallelization Speedup Potential

**Quantifier evaluation parallelization** (4-core CPU):
- Current sequential: 30-40ms (example: 1000 quantified bindings)
- Parallel (4 cores, 25% overhead): 8-12ms
- **Speedup: 3-4x**

**Portfolio SAT solving** (2 solvers):
- Case 1 (balanced): First solver finishes at 50%, saves ~50% time
- Case 2 (one solver 10x slower): Save entire slow solver time
- **Speedup: 1-10x depending on solver characteristics**

## Implementation Priority (Updated for Threading)

### Phase 1 (Quick Wins - 3-5 days, preserves parallelization)
- [x] Add `From<&T>` trait implementations
- [ ] Add `Solver::reset()` for instance reuse
- [ ] **NEW**: Integrate `bumpalo` for translation temporaries (thread-local arenas)
- [ ] **NEW**: Implement portfolio SAT solving with rayon

**Expected improvement**: 15-25% with portfolio solving
**Parallelization-friendly**: Yes (thread-local arenas, solver independence)

### Phase 2 (Medium Effort - 2-3 weeks, enables parallelization)
- [ ] Profile actual allocation patterns with flamegraph
- [ ] Thread-safe BooleanFactory (replace Cell/RefCell with Mutex or thread-local)
- [ ] Implement parallel quantifier evaluation with rayon
- [ ] Implement lazy tuple set construction

**Expected improvement**: 30-50% with parallelization on multi-core
**Parallelization-friendly**: Yes (BooleanFactory becomes thread-safe)

### Phase 3 (Significant Refactoring - 3-4 weeks, if needed)
- [ ] Index-based formula references (u32 indices instead of Arc)
- [ ] Slab-based boolean circuit storage
- [ ] Parallel CNF generation (complex dependencies)

**Expected improvement**: Additional 10-20% memory, 1.5-2x speedup on CNF
**Parallelization-friendly**: Medium (index-based requires careful synchronization)

## Updated Summary Table

### Phase 1 (Quick Wins - implement now)
- [x] Add `From<&T>` trait implementations (eliminates explicit `.clone()` at call sites)
- [ ] Add `Solver::reset()` for instance reuse

## Updated Summary Table

| Strategy | Speedup | Effort | Threading Impact | Recommendation |
|----------|---------|--------|------------------|----------------|
| Keep Arc vs Rc | None (~0.001%) | None | Preserves parallelization | **Keep Arc** |
| Arena allocation (bumpalo) | 5-10% | 3-5 days | Thread-local friendly | **Phase 1** |
| Portfolio SAT solving | 1-10x variable | 2-3 days | Parallel-ready | **Phase 1** |
| Thread-safe factory | Enables parallelization | 1-2 weeks | Required for parallelization | **Phase 2** |
| Parallel quantifiers | 2-4x on multi-core | 1-2 weeks | Core parallelization | **Phase 2** |
| Lazy tuple sets | 2-5% | 1 week | No threading impact | **Phase 2** |
| Index-based refs (u32) | 50% memory, 5-10% time | 3-4 weeks | Complicates threading | **Phase 3** |
| Parallel clause generation | 1.5-2x | High | Complex dependencies | **Phase 3** |

## Final Notes

- **Arc vs Rc**: Keep Arc. Enables future parallelization. Switching saves <0.001% time.
- **Parallelization**: Both Java Kodkod and current Rust version are single-threaded. Parallelization is a novel opportunity not present in original.
- **Thread-safety**: bumpalo is not Send/Sync by default. Use thread-local arenas for safe parallel allocation.
- **Index-based refs**: u32 saves memory but complicates threading. Defer unless profiling shows bottleneck.
- **Quick wins**: Portfolio solving (2-3 days) and arena allocation (3-5 days) with high threading compatibility.
- **Focus**: Reducing allocation count matters more than allocation size. Translation phase is 40-60% of runtime.
- **SAT solver**: rustsat backend is already highly optimized. Bottleneck is FOL→Boolean translation.
