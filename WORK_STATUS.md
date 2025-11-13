# Examples and Benchmarking Status Report

## Completed Work

### 1. Documentation Updates
- ✅ **sudoku.rs**: Removed outdated comment about formula evaluation issues (sudoku now works correctly)

### 2. Handshake Bug Investigation
- ✅ **Created debug_handshake.rs**: Minimal test cases isolating the problem
- ✅ **Identified Root Cause**: Count expressions with multiple quantified variables fail
  - Test 1 (simple count): ✓ SAT
  - Test 2 (forall + count vs constant): ✓ SAT
  - Test 3 (forall + two vars comparing counts): ✗ UNSAT (0 vars, 1 clause)
  - Test 4 (with disjoint constraint): ✗ UNSAT (0 vars, 1 clause)

**Issue**: When comparing integer counts of two different universally quantified variables
(e.g., `all p, q: Person | p.shaken.count() != q.shaken.count()`), the formula evaluates to
FALSE during translation, resulting in trivially UNSAT with 0 variables.

**Root Cause**: Likely in the FOL→Boolean translator's handling of integer expressions
with multiple quantified variables. Needs deep debugging in the translator module.

### 3. Benchmark Infrastructure
- ✅ **Added criterion dependency** with HTML report support
- ✅ **Created benches/solver_benchmarks.rs**: Basic performance benchmarks on pigeonhole problems
  - Tests 3x3, 4x3, 5x4 problem sizes
  - Measures translation and solving time separately

- ✅ **Created benches/solver_comparison.rs**: Framework for comparing SAT solvers
  - Currently uses batsat backend
  - Can be extended to test MiniSat, CaDiCaL, Kissat via rustsat
  - Parameterized benchmarks for easy scaling

- ✅ **Configured Cargo.toml** for criterion benchmarks with HTML reports

## Pending Work

### Examples (6 examples from Java Kodkod)
- GraphColoring (CSP)
- Lists (data structures)
- Trees (data structures)
- Hotel (temporal logic)
- FileSystem (practical modeling)
- NQueens (CSP) - complex due to API complexity

### Stress Tests
- Large N-Queens (100+)
- Large Sudoku (16x16)
- Large graph coloring (100+ nodes)

## Key Findings

### Sudoku Example
- **Status**: ✓ Working correctly
- Output shows complete, valid solutions
- No longer has the quantified formula issues mentioned in old comments

### Handshake Example
- **Status**: ✗ Broken for 3+ persons
- **2 persons**: SAT but with 0 handshakes (should have some)
- **3+ persons**: UNSAT with trivially unsatisfiable formula (0 vars, 1 clause)

### Pigeonhole Example
- **Status**: ✓ Fully working
- All test cases pass correctly:
  - 3 pigeons, 3 holes: SAT ✓
  - 4 pigeons, 3 holes: UNSAT ✓
  - 5 pigeons, 4 holes: UNSAT ✓

## Benchmark Usage

Run benchmarks with:
```bash
cargo bench --bench solver_benchmarks     # Basic solver performance
cargo bench --bench solver_comparison      # Solver comparison framework
```

HTML reports will be generated in `target/criterion/`.

## Next Steps for Fixing Handshake

To fix the Handshake bug, investigate:

1. **Translator module** (`src/translator/`):
   - How are integer expressions with multiple quantified variables handled?
   - Does variable substitution work correctly when 2+ variables are in scope?

2. **Specific failing pattern**:
   - `all p, q: Person | p.shaken.count() != q.shaken.count()`
   - Compare with working pattern:
   - `all p: Person | p.shaken.count() > -1`

3. **Root cause hypotheses**:
   - Variable binding in `LeafInterpreter`
   - Integer expression simplification
   - Quantifier handling with multiple declarations
   - CNF translation of integer constraints

## Code References

- Debug test: `examples/debug_handshake.rs`
- Handshake example: `examples/alloy_handshake.rs`
- Benchmarks: `benches/solver_benchmarks.rs`, `benches/solver_comparison.rs`
- Translator: `src/translator/`
