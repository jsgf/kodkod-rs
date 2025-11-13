# Arena Allocation Implementation Status

## Completed (Session N)
- [x] Dependencies added: bumpalo 3.19, bumpalo-herd 0.1
- [x] MatrixArena abstraction created (src/bool/arena.rs)
- [x] PERFORMANCE_ANALYSIS.md updated with bumpalo_herd recommendation
- [x] Flamegraph confirmed allocation is the bottleneck

## Next Session: BooleanMatrix Refactoring (Phase 2)

### Strategy
Use **copy-on-write** approach: Each operation creates new HashMap, allocates in arena.

### Implementation Sequence

**Step 1: Update src/bool.rs struct definition** (Line ~323)
```rust
// Before:
pub struct BooleanMatrix {
    dimensions: Dimensions,
    cells: HashMap<usize, BoolValue>,
}

// After:
pub struct BooleanMatrix<'arena> {
    dimensions: Dimensions,
    cells: &'arena HashMap<usize, BoolValue>,
}
```

**Step 2: Fix BooleanMatrix::empty()** (Line ~331)
- Add arena parameter
- Return reference allocated in arena

**Step 3: Fix BooleanMatrix::with_bounds()** (Line ~351)
- Add arena parameter before _factory
- Build HashMap, allocate in arena

**Step 4: Fix iteration loops** (Lines 424, 430, 446, 500, 536, 559, 589, 634)
- Change `for (&idx, val) in &self.cells` to `for (&idx, val) in self.cells`
- Since cells is `&HashMap`, already a reference

**Step 5: Fix set() method** (Line ~378)
- Copy-on-write: clone cells, modify, allocate new
- Signature: `pub fn set(&self, index: usize, value: BoolValue, arena: &'arena MatrixArena) -> BooleanMatrix<'arena>`

**Step 6: Fix matrix operations** (union, intersection, difference, join, product, transpose, etc.)
- Add `arena: &'arena MatrixArena` parameter to each method
- Build new HashMap, allocate in arena: `arena.alloc(result_map)`

**Step 7: Update BooleanFactory::matrix()** (src/bool/factory.rs line ~260)
- Add arena parameter
- Pass to BooleanMatrix::empty(dimensions, arena)

**Step 8: Update Environment** (src/translator/environment.rs)
- Add lifetime: `pub struct Environment<'arena>`
- Change bindings to `Vec<(Variable, BooleanMatrix<'arena>)>`

**Step 9: Update Translator** (src/translator.rs)
- Add lifetime to FOL2BoolTranslator<'arena>
- Store arena: `arena: &'arena MatrixArena`
- Thread through all methods

**Step 10: Update Solver** (src/solver.rs)
- Create MatrixArena in solve()
- Pass to Translator::evaluate()

### Verification
After each step:
```bash
cargo check 2>&1 | head -50
```

### Testing
```bash
cargo test --lib
cargo build --release --examples
cargo run --release --example sudoku
cargo run --release --example trees  # Should be faster
```

### Files to Modify
1. src/bool.rs (matrix struct, methods)
2. src/bool/factory.rs (factory.matrix() calls)
3. src/translator/environment.rs (Environment struct)
4. src/translator.rs (FOL2BoolTranslator)
5. src/translator/leaf_interpreter.rs (interpreter methods)
6. src/solver.rs (arena creation)

### Key Design Decisions
- **Lifetime scope**: 'arena is scoped to translation phase (Solver::solve)
- **Copy-on-write**: Simpler than trying to mutate in place
- **Public API unchanged**: MatrixArena is internal detail

### Performance Target
- 10-30% faster translation
- 60-80% fewer allocations
- Trees example scope 3+ should complete (currently times out)

### Notes for Implementation
- Don't use ahash yet (can be simple find+replace later)
- Focus on correctness first, performance second
- All examples must pass tests
- Benchmark before/after with criterion
