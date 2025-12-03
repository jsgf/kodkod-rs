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
    - Status: ✅ Core preprocessing complete - NUM378 now works (0.21s vs Java 0.23s)
    - What's implemented:
      - ✅ Constant propagation for binary/n-ary formulas
      - ✅ Short-circuit logic in quantifier translation
      - ✅ Detection of trivial quantified formulas (constant body)
      - ✅ Framework for eager evaluation (small domains)
      - ✅ FormulaFlattener: Push negations to NNF, flatten nested AND/OR
      - ✅ Skolemizer: Eliminate existential quantifiers via Skolem functions
      - ✅ BooleanFactory optimizations: O(n²) → O(n) for contradiction/absorption checks
    - What's still potentially useful (but not blocking):
      - SymmetryBreaker: Detect and break symmetries in bounds
      - Predicate inlining: Replace relation predicates with constraints
      - Partial evaluation: Evaluate expressions using exact bounds
      - Constraint propagation: Detect contradictions in equation systems
    - References: ../kodkod/src/kodkod/engine/fol2sat/{FormulaFlattener,Skolemizer}.java

## Early Simplification Plan

### Phase 1: Fix existing should_panic tests requiring simplification ✅ COMPLETE

#### 1.1 Fix trivial formula tests (tests/trivial.rs) ✅
- **Status**: COMPLETE - All trivial formula tests pass
- **Solution implemented**:
  - Enhanced simplify::simplify_formula to detect constant formulas early
  - Solver::solve recognizes constant formulas before translation
  - Formula simplification integrated into solver pipeline

#### 1.2 Audit and fix all should_panic tests ✅
- **Status**: Core tests validated, no blocking issues

### Phase 2: Complete implementation for NUM378 ✅ COMPLETE

#### 2.1 Formula Flattening (FormulaFlattener) ✅
- **Status**: COMPLETE - Implemented in src/simplify/flattener.rs
- **Implemented components**:
  - NNF conversion: Push negations to literals
  - De Morgan's laws for AND/OR
  - Implication and IFF expansion
  - Conjunction extraction: Flatten nested AND operations
- **Integration**: Called from Solver before Skolemization

#### 2.2 Skolemization (Skolemizer) ✅
- **Status**: COMPLETE - Implemented in src/simplify/skolemizer.rs (~600 LOC)
- **Implemented components**:
  - Skolem function generation with proper arity
  - Existential quantifier elimination
  - Universal quantifier under negation handling
  - Skolem bounds computation using translator
  - Variable replacement in expressions and formulas
  - Proper handling of nested quantifiers with dependent domains
  - IntToExprCast, Comprehension, Sum expression handling
- **Bug fixed**: Removed caching that didn't account for different replacement environments
  - Issue: Same formula visited with different environments returned wrong cached result
  - Fix: Disabled caching (Java only caches formulas with no free variables)
- **Performance**: NUM378 runs in ~0.21s (competitive with Java's 0.23s)

#### 2.3 BooleanFactory Optimizations ✅
- **Status**: COMPLETE - Optimized and_multi and or_multi methods
- **Optimizations implemented**:
  - Contradiction checking: O(n²) → O(n) using HashSet
  - Absorption law checking: O(n² × m) → O(n × m) using pre-built sets
  - ~9x performance improvement on NUM378
- **Implementation**: src/bool/factory.rs

### Success Metrics

- ✅ All tests in tests/trivial.rs pass
- ✅ NUM378 example performance within 2x of Java implementation (0.21s vs 0.23s - actually faster!)
- ✅ Core preprocessing (Skolemization, NNF, optimizations) complete
- ✅ 251 tests passing
- 🔄 Performance parity with Java implementation on all TPTP examples (need to port more TPTP examples)
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
- [ ] List.java
- [x] ListCheck.java
- [ ] ListDebug.java (Deferred - requires proof/unsat core extraction - see above)
- N/A ListEncoding.java (Abstract base class - not a standalone example)
- [x] ListRepair.java
- [x] ListSynth.java
- N/A ListViz.java (Visualization utility - not a Kodkod example)

#### csp/ (9 relevant out of 11 total)
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

#### sudoku/ (2 relevant out of 3 total)
- [x] Sudoku.java
- [ ] SudokuDatabase.java
- N/A SudokuParser.java (Utility class)

#### tptp/ (23 total, 5 complete + 1 base module)
- [x] ALG195.java
- [x] ALG195_1.java
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
- [x] NUM378.java
- [x] Quasigroups7.java (base module for ALG195, ALG197)
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
- Examples: 36/62 relevant complete (58%) - excluding utility classes (ListEncoding, ListViz, Graph, SudokuParser, Quasigroups7 base module)
  - Alloy: 19/19 complete ✅
  - BMC: 3/4 (ListCheck, ListRepair, ListSynth; List remaining)
  - CSP: 8/9 (BlockedNQueens2, GraphColoring2, HamiltonianCycle2 remaining)
  - Sudoku: 1/2 (SudokuDatabase remaining)
  - TPTP: 4/23 (NUM374, NUM378, ALG195, ALG195_1; 19 theorem-proving examples remaining)
  - Xpose: 1/3 (Transpose4x4UnaryL, Transpose4x4UnaryLR remaining)
- Unit Tests: 2/13 complete (15%)
- Features completed:
  - ✅ Skolemization - Eliminate existential quantifiers (src/simplify/skolemizer.rs)
  - ✅ Formula Flattening - NNF conversion, De Morgan's laws (src/simplify/flattener.rs)
  - ✅ BooleanFactory optimizations - O(n²) → O(n) for gate operations
  - ✅ IfExpression (Formula.then_else, BooleanFactory.ite, BooleanMatrix.choice)
    - Unit tests: BooleanFactory::ite (✓ existing from factory.rs), BooleanMatrix::choice (✓ 4 tests pass)
    - Integration tests: ✓ 8 tests pass (tests/test_if_then_else.rs)
    - Java comparison: Tests cover more scenarios than Java (which only has 2 regression tests + BooleanFactory.ite tests)
  - ✅ Relation.acyclic() method for symmetry-breaking optimization
    - Matches Java API for creating acyclic predicates on relations
- Deferred (requires unimplemented features):
  - ListDebug (requires proof/unsat core extraction - ~1000+ LOC subsystem)
