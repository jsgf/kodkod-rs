# Kodkod-rs TODO

## Remaining Work

### Examples to Port (5 remaining out of 62 relevant)

**BMC** (2 remaining):
- [ ] List.java
- [ ] ListDebug.java (Unblocked - proof/unsat core extraction complete)

**CSP** (3 remaining):
- [ ] BlockedNQueens2.java
- [ ] GraphColoring2.java
- [ ] HamiltonianCycle2.java

**Sudoku** (1 remaining):
- [ ] SudokuDatabase.java

### Tests to Port (3 remaining out of 13)

- [ ] IncrementalSolverTest.java (BLOCKED: requires IncrementalSolver class ~500 LOC)
- [ ] ReductionAndProofTest.java (unblocked - needs adaptation for deletion-based minimization)
- [ ] SparseSequenceTest.java (internal data structures - may not be needed)

**System Tests:**
- [ ] ExamplesTest.java (tests that examples run)

### Remaining Tasks

- Fix up copyrights
  - All files should have the same copyright and license as the Java files they're derived from
  - The overall package should have the same license
- Fix up documentation
  - All public Rust interfaces should have doc comments
  - Where possible, have examples as doc tests
- Lint audit
  - Core compiler warnings (non-clippy) should always be fixed
  - Audit clippy lint warnings
- Audit code for use of `unsafe` and validate with user
- Analyze use of .clone() in API
  - Examples have many .clone() calls - analyze if API can minimize these
  - Consider arena allocator expansion for Copy semantics
- Revisit arena allocator implementation
  - Current: 9 unsafe blocks in src/bool/arena.rs
  - Options: expand arena usage vs revert to Rc
  - Benchmark performance difference

### Known Limitations (documented in code comments)

These are valid implementation details that don't need immediate action:

**src/solver.rs:**
- Line 158: TODO: populate TriviallySat instance with lower bounds
- Line 668: TODO: Generate proof during iteration (SolutionIterator)

**src/translator.rs:**
- Line 837: Dynamic shift not yet supported
- Line 940: Sum over declarations not yet supported

**src/simplify/skolemizer.rs:**
- Line 65: TODO: Implement caching that considers free variables
- Line 412: TODO: Implement full Java Environment tracking for parameter crossing

**src/translator/leaf_interpreter.rs:**
- Line: TODO: support int_bounds when needed

**src/instance.rs:**
- TODO: Switch API - make `new()` take `Vec<Rc<dyn Atom>>`, add `from_str()` for backward compat

---

## Completed Work

### ✅ Examples Ported (57/62 relevant = 92%)

All examples have #[test] functions (58/60 with tests = 97%):
- Excluded from tests: alloy_viktor.rs (too long-running), tptp_quasigroups7.rs (base module)
- 69 example test functions total, all passing

**Alloy (19/19)** ✅
- AbstractWorldDefinitions, Bigconfig, CeilingsAndFloors, DiffEg, Dijkstra
- DNACuts, FileSystem, GroupScheduling, Handshake, Hotel
- Lists, Netconfig, Pigeonhole, RingElection, Toughnut
- ToyFilesystem, ToyLists, Trees, Viktor

**BMC (2/4)**
- ListCheck, ListRepair, ListSynth

**CSP (6/9)**
- BlockedNQueens, GraphColoring, HamiltonianCycle
- LatinSquare, MagicSeries, NQueens, SocialGolfer

**Sudoku (1/2)**
- Sudoku

**TPTP (23/23)** ✅
- ALG195, ALG195_1, ALG197, ALG212
- COM008, GEO091, GEO092, GEO115, GEO158, GEO159
- GRA013_026, LAT258, MED001, MED007, MED009
- MGT066, NUM374, NUM378, Quasigroups7 (base module)
- SET943, SET948, SET967, TOP020

**Xpose (3/3)** ✅
- Transpose4x4, Transpose4x4UnaryL, Transpose4x4UnaryLR

### ✅ Tests Ported (10/13 = 77%)

**327 tests passing across 24 test suites**

- ✅ BooleanCircuitTest.java (20 tests in src/bool/factory.rs)
- ✅ BooleanMatrixTest.java (partial coverage)
- ✅ EnumerationTest.java (3 tests in tests/test_enumeration.rs)
- ✅ EvaluatorTest.java (22 tests in tests/test_evaluator.rs)
- ✅ IntTest.java
- ✅ RegressionTests.java (5 tests, proof tests skipped)
- ✅ SkolemizationTest.java (7 tests in tests/test_skolemization.rs)
- ✅ SymmetryBreakingTest.java (2 tests in tests/test_symmetry_breaking.rs)
- ✅ TranslatorTest.java (26 tests in tests/test_translator.rs)
- ✅ UCoreTest.java (3 tests in tests/test_ucore.rs)

### ✅ Major Features Implemented

#### Formula Preprocessing & Optimization
- ✅ **FormulaFlattener** (src/simplify/flattener.rs)
  - NNF conversion, De Morgan's laws
  - Implication and IFF expansion
  - Conjunction extraction and flattening
- ✅ **Skolemizer** (src/simplify/skolemizer.rs ~600 LOC)
  - Skolem function generation with proper arity
  - Existential quantifier elimination
  - Nested quantifier handling with dependent domains
  - IntToExprCast, Comprehension, Sum expression handling
- ✅ **BooleanFactory Optimizations**
  - Contradiction checking: O(n²) → O(n) using HashSet
  - Absorption law: O(n² × m) → O(n × m)
  - ~9x performance improvement
- ✅ **Constant propagation** for binary/n-ary formulas
- ✅ **Short-circuit logic** in quantifier translation
- ✅ **Trivial formula detection** (constant body in quantifiers)

#### Proof & Unsat Core Extraction (~850 LOC)
- ✅ **TranslationLog and TranslationRecord** (src/proof.rs)
- ✅ **Proof struct** with core(), log(), minimize() methods
- ✅ **Options fields**: log_translation, core_granularity (0-3)
- ✅ **Solution proof fields** for Unsat/TriviallyUnsat
- ✅ **Trivial proof minimization** using deletion-based approach with actual solving
- ✅ **Non-trivial proof extraction** using assumption-based cores from batsat
- ✅ **SATSolver::solve_with_assumptions()** and unsat_core() methods
- ✅ **Minimal core verification** (12 tests: 6 proof + 3 unsat_core + 3 UCoreTest)

**Implementation approach:**
- Uses deletion-based minimization instead of Java's RCE/SCE strategies
- Java uses ResolutionTrace with full resolution graph (antecedents, learnable, backwardReachable)
- batsat provides assumption-based cores but no resolution graph API
- CaDiCaL has TraceProof with antecedents (could enable resolution strategies in future)
- Current approach is simpler but complete - produces minimal cores correctly

#### Symmetry Breaking
- ✅ **SymmetryBreaker** (src/engine/symmetry_breaker.rs)
  - Aggressive mode achieves Java parity on variable reduction
  - TotalOrdering: 0 primary vars (Java: 0)
  - Acyclic: 10 primary vars for 5x5 (Java: 10)
  - Tests: tests/test_symmetry_breaking.rs

#### Other Features
- ✅ **IfExpression** (Formula.then_else, BooleanFactory.ite, BooleanMatrix.choice)
  - 8 integration tests (tests/test_if_then_else.rs)
  - More comprehensive than Java tests
- ✅ **Relation.acyclic()** method for symmetry-breaking optimization
- ✅ **Solution enumeration** (solveAll) with SolutionIterator
  - Returns iterator over all satisfying instances
  - Adds blocking clauses to exclude previous solutions
  - Distinguishes TRIVIALLY_SAT (lower bounds) from SAT (solver found)
- ✅ **FOL2BoolCache** parity with Java (src/translator/cache.rs ~500 LOC)
  - Subsumption detection: `(a & b) & (a & b & c) = (a & b & c)`
  - Absorption law: `p AND (p OR q) = p` and `p OR (p AND q) = p`

### ✅ Performance Achievements

- **NUM378**: 0.21s (Rust) vs 0.23s (Java) - Rust is faster!
- **Translation**: Often 5x faster than Java despite more CNF variables
- **Solving**: Frequently faster despite 1.7x more CNF variables
- **Core preprocessing**: Complete and competitive with Java

### ✅ Investigations Completed

#### CNF Size Difference (Transpose4x4UnaryL)
- Java: 10533 vars, 36835 clauses (translation 109ms, solving 1026ms)
- Rust: 18132 vars, 41792 clauses (translation 20ms, solving ~400ms)
- Root cause identified: Java's BooleanFactory uses Assembler pattern with 15 specialized handlers
- Would require ~500 LOC architectural rewrite for parity
- Decision: Accept difference - Rust is still faster overall

---

## Notes

1. **Nothing is complete** unless at least `cargo check` of all targets passes
2. **All features must have tests**, ideally ported from Java equivalents
3. **Commit work** between major steps
4. **Port philosophy**: Complete, accurate, and faithful to Java implementation
5. **No stubs/placeholders**: Tests should fail if implementation incomplete
