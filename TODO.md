- Port all remaining examples
  - The primary goal of this is to discover any missing features or bugs
  - Secondary goal is to make idiomatic Rust versions which are functionally identical to the Java
  - If an example fails because of a bug or missing feature, then you *MUST* fix the bug or implement the feature before moving on.
  - **EXCEPTION**: Features requiring substantial subsystems (>500 LOC) can be deferred and documented below
  - **RELEVANT EXAMPLES**: Only examples that actually use the Kodkod API are tracked. Support files (List.java, Graph.java, parsers, databases) are excluded.
- Port all remaining tests
  - Make sure there's a Rust test corresponding to every Java test
  - Like examples, *DO NOT* move on if there's a bug or missing feature
    - If, after explicit permission, there's a reason to skip a test for now, leave the test in a *failing* or with a `#[should_panic]` annotation so the gap is obvious
  - This excludes tests which are only specific to Java, like the JNI interfaces to solvers, or custom data structures which Rust has by default
- After all examples are ported, add #[test] functions to examples
  - Examples should keep their main() functions (for standalone execution)
  - Add #[test] functions that invoke main functionality and assert expected outcomes
  - This allows `cargo test` to validate all examples work correctly
  - May require minor refactoring to expose testable functions
- Implement missing optimizations
  - Revisit all should_panic tests and implement the features they require
  - **PERFORMANCE: Formula preprocessing for complex quantified formulas**
    - Status: Basic constant propagation implemented, deeper preprocessing needed
    - What's implemented:
      - Constant propagation for binary/n-ary formulas
      - Short-circuit logic in quantifier translation
      - Detection of trivial quantified formulas (constant body)
      - Framework for eager evaluation (small domains)
    - What's still needed for NUM378 (92 vars over 22 atoms):
      - FormulaFlattener: Push negations, flatten to CNF
      - Skolemizer: Eliminate existentials via Skolem functions
      - SymmetryBreaker: Detect and break symmetries in bounds
      - Predicate inlining: Replace relation predicates with constraints
      - Partial evaluation: Evaluate expressions using exact bounds
      - Constraint propagation: Detect contradictions in equation systems
    - Complexity: ~2000-3000 LOC across multiple modules
    - References: ../kodkod/src/kodkod/engine/fol2sat/{FormulaFlattener,Skolemizer}.java

## Early Simplification Plan

### Phase 1: Fix existing should_panic tests requiring simplification

#### 1.1 Fix trivial formula tests (tests/trivial.rs)
- **Problem**: Tests for TRUE, FALSE, TRUE∧FALSE, TRUE∨FALSE are failing
- **Root cause**: Early simplification of constant formulas not detecting trivial cases
- **Solution**:
  - Enhance simplify::simplify_formula to detect constant formulas early
  - Return Formula::TRUE/FALSE directly when formulas simplify to constants
  - Ensure Solver::solve recognizes constant formulas before translation
- **Test coverage**:
  - tests/trivial.rs (4 tests)
  - Add unit tests in src/simplify/mod.rs for constant detection

#### 1.2 Audit and fix all should_panic tests
- **Scope**: Review all tests with #[should_panic] attributes
- **Current inventory** (from grep):
  - src/ast.rs:500, 567 - Arity validation tests
  - src/translator/leaf_interpreter.rs:403 - Bounds checking
  - tests/test_if_then_else.rs:29 - Arity mismatch
  - src/bool/factory.rs:572, 639, 662, 737, 768, 799 - Boolean simplification
  - src/bool.rs:926, 932 - Variable label validation
  - tests/test_boolean_matrix.rs:492 - Transpose validation
- **Action**: Verify each test, ensure proper implementation exists

### Phase 2: Complete implementation for NUM378

#### 2.1 Formula Flattening (FormulaFlattener)
- **Purpose**: Convert formulas to Negation Normal Form (NNF) and break up quantifiers
- **Key components**:
  - NNF conversion: Push negations to literals
  - Quantifier breakup: Split universal quantifiers when possible
  - Conjunction extraction: Flatten nested AND operations
- **Implementation path**:
  - Port ../kodkod/src/kodkod/engine/fol2sat/FormulaFlattener.java (~275 LOC)
  - Create src/simplify/flattener.rs
  - Integration point: Call from Solver before translation
- **Test coverage**:
  - Port Java tests from kodkod.test.unit.SkolemizationTest
  - Add regression tests for NUM378 preprocessing

#### 2.2 Skolemization (Skolemizer)
- **Purpose**: Eliminate existential quantifiers by introducing Skolem functions
- **Key components**:
  - Skolem function generation
  - Existential quantifier elimination
  - Dependency tracking for nested quantifiers
- **Implementation path**:
  - Port ../kodkod/src/kodkod/engine/fol2sat/Skolemizer.java (~564 LOC)
  - Create src/simplify/skolemizer.rs
  - Handle nested quantifier dependencies
- **Test coverage**:
  - Port Java SkolemizationTest
  - Verify on TPTP examples with heavy quantification

#### 2.3 Enhanced Constant Propagation
- **Current state**: Basic binary/n-ary propagation exists
- **Enhancements needed**:
  - Expression evaluation with exact bounds
  - Relation predicate evaluation when bounds are exact
  - Integer expression constant folding
  - Cardinality constraint simplification
- **Implementation**:
  - Extend src/simplify/mod.rs
  - Add Expression visitor for constant evaluation
  - Cache evaluated subexpressions

#### 2.4 Partial Evaluation with Bounds
- **Purpose**: Evaluate expressions using known bounds
- **Components**:
  - Exact bound detection (lower = upper)
  - Expression evaluation with substitution
  - Relation composition with known values
- **Implementation**:
  - Add bounds parameter to simplify_formula
  - Create evaluator for expressions with exact bounds
  - Integrate with constant propagation

#### 2.5 Integration and Optimization
- **Solver pipeline**:
  1. Initial simplification (constant propagation)
  2. Formula flattening (NNF conversion)
  3. Skolemization (if enabled)
  4. Partial evaluation with bounds
  5. Final simplification pass
- **Caching strategy**:
  - Cache simplified subformulas
  - Share cache across simplification phases
  - Use arena allocation for intermediate formulas

### Phase 3: Rust vs Java Audit

#### 3.1 Feature Comparison
- **Method**: Systematic comparison of Java and Rust implementations
- **Scope**:
  - Formula simplification (kodkod.engine.fol2sat.*)
  - Boolean circuit optimization (kodkod.engine.bool.*)
  - Translation optimizations (kodkod.engine.fol2sat.Translator)
- **Output**: Gap analysis document listing missing optimizations

#### 3.2 Performance Optimizations
- **Java optimizations to port**:
  - Circuit-level simplifications in BooleanFactory
  - Gate-level optimizations (absorption, idempotence)
  - CNF minimization techniques
- **Rust-specific optimizations**:
  - Arena allocation for formula nodes
  - Zero-copy formula transformations
  - Parallel simplification where applicable

#### 3.3 Test Coverage Alignment
- **Goal**: Ensure Rust tests cover all Java test scenarios
- **Process**:
  - Map Java test files to Rust equivalents
  - Identify missing test scenarios
  - Port or create equivalent tests
- **Priority areas**:
  - TPTP examples (especially NUM378)
  - Quantifier-heavy formulas
  - Large formula optimization

### Implementation Order & Dependencies

1. **Immediate** (Phase 1.1): Fix trivial formula tests
   - Required for basic solver correctness
   - Blocks other solver tests

2. **Short-term** (Phase 1.2 + 2.3): Enhanced constant propagation
   - Foundation for other optimizations
   - Improves existing examples

3. **Medium-term** (Phase 2.1-2.2): Flattener & Skolemizer
   - Required for NUM378
   - Enables quantifier-heavy examples

4. **Long-term** (Phase 2.4-2.5 + Phase 3): Full optimization suite
   - Performance improvements
   - Complete Java parity

### Success Metrics

- All tests in tests/trivial.rs pass
- NUM378 example performance within 2x of Java implementation
- No #[should_panic] tests that should be working
- Performance parity with Java implementation (within 2x) on all TPTP examples
- **Implement proof/unsat core extraction system**
  - Required for: ListDebug.java example
  - Scope: ~1000+ LOC across multiple modules
  - Components needed:
    - TranslationLog and TranslationRecord (~200 LOC) - track formula→CNF mapping during translation
    - Proof trait with TrivialProof and ResolutionBasedProof implementations (~530 LOC)
    - Core minimization strategies (RCEStrategy, etc.) (~134+ LOC each, multiple strategies)
    - SAT solver with proof support (MiniSatProver) - may require switching from batsat or adding proof tracking
    - Integration into Solver to enable options like setCoreGranularity() and setLogTranslation()
  - Status: Deferred due to complexity; blocks 1 example (ListDebug)
  - Following Java: kodkod.engine.Proof, kodkod.engine.fol2sat.TranslationLog, kodkod.engine.ucore.*
- Fix up copyrights
  - All files should have the same copyright and license as the Java files they're derived from
  - The overall package should have the same license
- Fix up documentation
  - All public Rust interfaces should have doc comments. These should be copied from Java (and ideally not reference the Java as this should be usable standalone)
  - Where possible, have examples as doc tests, and make them real tests (ie they must pass).
  - Use normal doc test features so only the essence is actually part of the example (ie no need to make use statements or other setup visible; example should just focus on the API in question and anything that's immediately relevant).
- Lint audit
  - Core compiler warnings (non-clippy) should always be fixed
    - make sure that "unused variable/function/argument/etc" warnings are not the result of some missing or unimplemented feature
  - Audit clippy lint warnings
    - Not all are worth acting on, but some are. Let's see what's there and decide what to do.
- Audit code for use of `unsafe` and validate *EVERY* *SINGLE* *INSTANCE* with user.
- Analyze use of .clone() in API
  - Examples seem to have a lot of them. Ultrathink a detailed analysis to see if these are really necessary, or if the API can be changed to minimize the need for them
  - One thing to consider is that the code using an arena allocator with Handles does not need this, since Handle is Copy and anything wrapping Handle could also be Copy
  - Also does everything that takes something by value actually need to? Could it take a reference. (But it *should not* take a reference then immediately clone it.)

NOTES:
1. *NOTHING* can be considered completed or done unless at least `cargo check` of all targets passes
2. Any newly implemented feature *must* also have tests, ideally ported from the equivalent Java ones.
4. Commit work between steps above.

---

## Progress Checklist

### Examples to Port

#### alloy/ (19 total)
- [x] AbstractWorldDefinitions.java
- [x] Bigconfig.java
- [x] CeilingsAndFloors.java
- [x] DiffEg.java
- [x] Dijkstra.java
- [x] DNACuts.java
- [x] FileSystem.java
- [x] GroupScheduling.java
- [x] Handshake.java
- [x] Hotel.java
- [x] Lists.java
- [x] Netconfig.java
- [x] Pigeonhole.java
- [x] RingElection.java
- [x] Toughnut.java
- [x] ToyFilesystem.java
- [x] ToyLists.java
- [x] Trees.java
- [x] Viktor.java

#### bmc/ (4 relevant out of 7 total)
- N/A List.java (Not a Kodkod example - it's the Java data structure being verified)
- [x] ListCheck.java
- [ ] ListDebug.java (Deferred - requires proof/unsat core extraction - see above)
- [x] ListEncoding.java
- [x] ListRepair.java
- [x] ListSynth.java
- N/A ListViz.java (Visualization helper - not a Kodkod example)

#### csp/ (9 relevant out of 10 total)
- [x] BlockedNQueens.java
- [ ] BlockedNQueens2.java
- N/A Graph.java (Support class - not a Kodkod example)
- [x] GraphColoring.java
- [ ] GraphColoring2.java
- [x] HamiltonianCycle.java
- [ ] HamiltonianCycle2.java
- [x] LatinSquare.java
- [x] MagicSeries.java
- [x] NQueens.java
- [x] SocialGolfer.java

#### sudoku/ (1 relevant out of 3 total)
- [x] Sudoku.java
- N/A SudokuDatabase.java (Support class)
- N/A SudokuParser.java (Support class)

#### tptp/ (24 total, 1 complete, 1 deferred)
- [ ] ALG195.java
- [ ] ALG195_1.java
- [ ] ALG197.java
- [ ] ALG212.java
- [ ] COM008.java
- [ ] GEO091.java
- [ ] GEO092.java
- [ ] GEO115.java
- [ ] GEO158.java
- [ ] GEO159.java
- [ ] GRA013_026.java
- [ ] LAT258.java
- [ ] MED001.java
- [ ] MED007.java
- [ ] MED009.java
- [ ] MGT066.java
- [x] NUM374.java
- [D] NUM378.java (Deferred - requires formula simplification before quantifier expansion - 92 vars)
- [ ] Quasigroups7.java
- [ ] SET943.java
- [ ] SET948.java
- [ ] SET967.java
- [ ] TOP020.java

#### xpose/ (3 total)
- [x] Transpose4x4.java
- [ ] Transpose4x4UnaryL.java
- [ ] Transpose4x4UnaryLR.java

### Tests to Port

#### Unit Tests
- [ ] BooleanCircuitTest.java
- [x] BooleanMatrixTest.java (partial)
- [ ] EnumerationTest.java
- [ ] EvaluatorTest.java
- [ ] IncrementalSolverTest.java
- [x] IntTest.java
- [ ] ReductionAndProofTest.java
- [ ] RegressionTests.java
- [ ] SkolemizationTest.java
- [ ] SparseSequenceTest.java
- [ ] SymmetryBreakingTest.java
- [ ] TranslatorTest.java
- [ ] UCoreTest.java

#### System Tests
- [ ] ExamplesTest.java (tests that examples run)

### Summary
- Examples: 28/61 relevant complete (46%) - excluding 5 support files (List.java, ListViz.java, Graph.java, SudokuDatabase.java, SudokuParser.java)
- Unit Tests: 2/13 complete (15%)
- Features completed:
  - IfExpression (Formula.then_else, BooleanFactory.ite, BooleanMatrix.choice)
    - Unit tests: BooleanFactory::ite (✓ existing from factory.rs), BooleanMatrix::choice (✓ 4 tests pass)
    - Integration tests: ✓ 8 tests pass (tests/test_if_then_else.rs)
    - Java comparison: Tests cover more scenarios than Java (which only has 2 regression tests + BooleanFactory.ite tests)
  - Relation.acyclic() method for symmetry-breaking optimization
    - Matches Java API for creating acyclic predicates on relations
- Deferred (requires unimplemented features):
  - ListDebug (requires proof/unsat core extraction - ~1000+ LOC subsystem)
  - ListViz (visualization helper, not critical for core functionality)
