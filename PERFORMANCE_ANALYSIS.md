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

## Profiling Recommendations

Before optimizing, profile with:

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

## Implementation Priority

### Phase 1 (Quick Wins - implement now)
- [x] Add `From<&T>` trait implementations (eliminates explicit `.clone()` at call sites)
- [ ] Add `Solver::reset()` for instance reuse

### Phase 2 (Medium Effort - improves 20-30%)
- [ ] Evaluate `bumpalo` integration for translation phase
- [ ] Profile actual allocation patterns with flamegraph
- [ ] Implement lazy tuple set construction

### Phase 3 (Significant Refactoring - improves 30-50%)
- [ ] Arena allocation for boolean circuits
- [ ] Slab-based formula cache with better locality
- [ ] Consider moving from Arc to arena-based references

## Expected Impact

**Current baseline**:
- Sudoku 4x4: ~20ms
- Graph Coloring 5v: ~50ms
- Trees 3v: >120s (timeout)

**After Phase 1**: ~5-10% improvement (less visible)
**After Phase 2**: ~20-30% improvement (becomes noticeable)
**After Phase 3**: ~40-50% improvement (significant for large problems)

## Notes

- Java Kodkod uses custom int collections + aggressive caching
- Rust's ownership model makes some Java optimizations harder to implement
- Focus on reducing allocation count before optimizing allocation size
- SAT solver itself (rustsat crate) is already highly optimized
- Bottleneck is likely FOL→Boolean translation, not SAT solving
