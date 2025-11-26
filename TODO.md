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
  - **PERFORMANCE: Formula simplification before quantifier expansion**
    - Issue: NUM378 hangs during translation (92 quantified vars over 22 atoms = 22^92 combinations)
    - Symptom: Formula evaluates to FALSE at innermost level, but must backtrack through all outer loops
    - Short-circuit helps but insufficient: FALSE OR FALSE = FALSE (never triggers short-circuit)
    - Java solution: Detects trivially UNSAT BEFORE expanding quantifiers
    - Root cause: Missing early formula preprocessing/simplification pass
    - Java does: FormulaFlattener.flatten(), Skolemizer.skolemize(), SymmetryBreaker, predicate inlining
    - We need: Pre-expansion constant propagation and contradiction detection
    - Status: Short-circuit logic added but not sufficient for this case
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

#### tptp/ (24 total)
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
- [ ] NUM378.java
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
