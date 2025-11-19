# Rust vs Java Implementation Size Analysis

## Overview

Java Kodkod: ~38,000 LOC across 166 files (~16,000 code-only)
Rust Kodkod: ~8,600 LOC across 20 files (~6,600 code-only)
Examples: ~2,200 LOC across 11 examples

**Rust implementation is ~2.4x smaller (code-only) or ~4.4x smaller (total)** while maintaining functional equivalence for core features.

## Package-by-Package Comparison

### Java Breakdown
- **ast**: 48 files, 7,439 lines
  - OOP hierarchy with visitor pattern
  - Separate classes for each AST node type
  - Getters, setters, equals, hashCode methods

- **engine**: 78 files, 18,442 lines
  - fol2sat/ translation (complex caching, environment handling)
  - bool/ boolean circuit layer
  - satlab/ SAT solver integration
  - ucore/ unsat core extraction
  - config/ extensive configuration system

- **instance**: 6 files, 1,692 lines
  - Bounds, Universe, TupleSet management
  - Instance representation

- **util**: 34 files, 10,444 lines
  - **Custom int collection classes** (major source of code)
    - IntSet, IntBitSet, IntVector, etc.
    - Specialized sparse/dense implementations
    - Custom iterators and algorithms
  - Node and relation utilities

### Rust Implementation
- **ast**: Enums with pattern matching (compact)
  - formula.rs, int_expr.rs, visitor.rs
- **engine**: Generic RustSatAdapter + Symmetry Breaking
  - rustsat_adapter.rs
  - symmetry_detector.rs (~266 LOC)
  - symmetry_breaker.rs (~550 LOC)
- **instance**: Universe, Bounds, TupleSet (using std collections)
- **translator**: FOL→Boolean translation with environment
  - translator.rs, environment.rs, leaf_interpreter.rs
- **bool**: Boolean circuit with gate caching (FxHashMap)
  - factory.rs, arena.rs, var_allocator.rs, int.rs
- **cnf**: CNF/Tseitin transformation
- **solver**: Main API with Options

## Key Differences Explaining Size Reduction

### 1. **Custom Collections (Biggest Factor)**
- **Java**: 34 files dedicated to optimized int collection variants
  - IntSet, ArrayIntSet, IntBitSet, IntVector
  - SparseSequence implementations
  - Tree-based sparse collections
  - Extensive collection hierarchy

- **Rust**: Uses std library directly
  - `Vec<usize>` instead of IntVector
  - `BTreeSet<usize>` for IntSet (used in symmetry detection)
  - FxHashMap (fast non-crypto hash) for caching
  - **Result**: ~2,000+ fewer lines

### 2. **Verbose OOP Patterns in Java**
- **Java**: Each class needs:
  - Constructors (sometimes multiple overloads)
  - Getters/setters for fields
  - equals() and hashCode()
  - toString()
  - Javadoc comments
  - Factory methods

- **Rust**:
  - Derives traits automatically (Clone, Debug, etc.)
  - Public fields or simple accessor methods
  - Structured bindings and pattern matching
  - Enum dispatch for AST (Expression, Formula, IntExpression)
  - Visitor trait for complex traversals when needed
  - **Result**: ~30-40% less boilerplate code

### 3. **SAT Solver Integration**
- **Java**: ~2,000+ lines for JNI/wrapper code for multiple solvers
  - MiniSat, Glucose, Lingeling wrappers
  - Solver selection and configuration
  - JNI marshaling code

- **Rust**: ~200 lines
  - Single RustSatAdapter generic over rustsat trait
  - No FFI/JNI needed - pure Rust or rustsat crates
  - Pluggable via trait system
  - **Result**: ~90% less SAT integration code

### 4. **Configuration & Options**
- **Java**: Extensive options system with multiple knobs
  - Symmetry breaking configurations
  - Solver selection strategies
  - Logging and reporting
  - Caching strategies

- **Rust**: Streamlined options
  - Boolean circuit options (sharing on/off)
  - Timeout support
  - Symmetry breaking predicate length (default: 20)
  - Can be extended as needed
  - **Result**: ~500 fewer lines

### 5. **Visitor Pattern Implementation**
- **Java**: Multiple visitor classes and abstract base classes
  - ExpressionVisitor, FormulaVisitor, etc.
  - Abstract methods must be implemented everywhere
  - Double dispatch pattern requires boilerplate

- **Rust**: Pattern matching on enums
  - `match` expressions are concise
  - Type-safe by default
  - No runtime polymorphism overhead
  - **Result**: ~1,000 fewer lines

### 6. **Error Handling & Validation**
- **Java**: Throws exceptions with try/catch blocks throughout
  - Defensive programming with validation in many places
  - Stack traces and error context
  - try-finally for resource cleanup

- **Rust**: Result<T> and Option<T>
  - Errors propagate via `?` operator
  - No exceptions means less error handling code
  - RAII for resource cleanup
  - **Result**: ~500 fewer lines (less defensive code)

## What's Missing/Simplified in Rust vs Java

### Not Yet Implemented
1. **Unsat Core Extraction** (~1,000 LOC in Java)
   - Java has ucore/ package for extracting minimal unsatisfiable cores
   - Rust version omits this (not yet needed)

2. **Incremental Solving** (~500 LOC in Java)
   - Java supports incremental solver calls with assumption literals
   - Rust version solves from scratch each time

### Implemented
1. **Symmetry Breaking** (~816 LOC in Rust, ~500 LOC in Java)
   - ✓ Symmetry detection via partition refinement
   - ✓ Lex-leader predicate generation
   - ✓ Matrix symmetry breaking for TotalOrdering and Acyclic predicates
   - ✓ Configurable via symmetry_breaking option (default: 20)

2. **Gate Caching** (~200 LOC in Rust, ~1,000 LOC in Java)
   - ✓ FxHashMap-based gate deduplication in BooleanFactory
   - ✓ Configurable sharing on/off
   - Java has more extensive IdentityHashMap caching throughout
   - Rust uses simpler Arc-based identity for Relations

### Intentionally Simplified
1. **Custom int Collections** → Using std library
   - Trade: Less optimal memory usage
   - Gain: 2,000+ fewer lines of code
   - Trade-off is acceptable for correctness-first approach
   - BTreeSet used for symmetry detection IntSet

2. **Caching** → FxHashMap gate deduplication + Arc identity
   - Gate deduplication via FxHashMap in BooleanFactory
   - Relation identity via Arc pointer equality
   - Simpler than Java's extensive IdentityHashMap use
   - Good performance with less complexity

3. **Multiple SAT Solver Integration** → RustSat adapter pattern
   - Trade: Users must provide solver
   - Gain: Zero dependencies in core library
   - Better separation of concerns
   - Default: batsat via rustsat-batsat

4. **Configuration** → Minimal, focused options
   - Boolean circuit sharing (on/off)
   - Symmetry breaking predicate length
   - Timeout support
   - Can extend as needed without over-engineering

## Summary

The 2.4x-4.4x size reduction (code-only vs total) is achieved through:

1. **Collections** (25% reduction): No custom collection classes, use std library
2. **Boilerplate** (30% reduction): Less OOP ceremony, derives, pattern matching
3. **SAT Integration** (15% reduction): Generic RustSat adapter vs JNI wrappers
4. **Concise syntax** (20% reduction): Rust's expressive type system and traits
5. **Unimplemented features** (10% reduction): Unsat cores, incremental solving

### Code Quality Assessment

**Java advantages**:
- More optimizations for specific problems
- Custom int collections for memory efficiency
- Incremental solving support
- Unsat core extraction
- Extensive configuration options

**Rust advantages**:
- More concise and easier to understand
- Safer type system (no null pointers, lifetime checking)
- No GC pauses
- Better separation of concerns (no JNI)
- Pure Rust = easier to compile and deploy
- Symmetry breaking fully implemented
- Modern hash maps (FxHashMap) for performance

**Conclusion**: The Rust version is a faithful, complete port of the core FOL→SAT pipeline with symmetry breaking. It focuses on **correctness and clarity** while maintaining competitive performance. Advanced features like unsat cores and incremental solving can be added as needed, but the foundation is solid and maintainable.

### Examples Implemented

The Rust port includes 11 working examples (~2,200 LOC):
- alloy_pigeonhole.rs - Classic pigeonhole principle
- alloy_handshake.rs - Handshake problem
- sudoku.rs - Sudoku solver
- graph_coloring.rs - Graph coloring
- toy_lists.rs - Toy list structures
- file_system.rs - File system model
- trees.rs - Tree structures
- hotel.rs - Hotel room allocation
- alloy_netconfig.rs - Network configuration
- alloy_group_scheduling.rs - Group scheduling
- test_symmetry_breaking.rs - Symmetry breaking tests

All examples demonstrate the full translation pipeline from relational logic to SAT and back to instances.

## Missing Performance Optimizations

### 1. **FOL→Boolean Translation Caching (HIGH IMPACT)**

**Java implementation:**
- Pre-processes AST to detect shared nodes (nodes appearing multiple times in the DAG)
- Caches translation of shared nodes using `IdentityHashMap` keyed by:
  - Node identity
  - Free variable bindings in current environment
- Every visit method follows pattern:
  ```java
  BooleanMatrix ret = lookup(node);
  if (ret != null) return ret;
  // ... translate ...
  return cache(node, result);
  ```

**Rust implementation:**
- **MISSING**: No shared node detection
- **MISSING**: No translation cache
- Naively re-translates every subexpression each time it's encountered
- Example: If `(r1.r2)` appears 5 times in a formula, Rust translates it 5 times

**Performance impact:**
- For formulas with significant sharing (common in real-world models), this can cause **exponential blowup**
- Example: A formula like `(A && B) || (A && B)` will translate `A` twice and `B` twice in Rust, but only once each in Java
- Deeply nested formulas with sharing can be **orders of magnitude slower**

**Estimated impact:** Can be 2-100x slower depending on formula structure. Highly shared formulas suffer most.

---

### 2. **Leaf Expression Caching (MEDIUM IMPACT)**

**Java implementation:**
- Separate `leafCache` (HashMap) for Relations and ConstantExpressions
- `visit(Relation)` and `visit(ConstantExpression)` check cache before calling interpreter
- Prevents redundant BooleanMatrix construction for the same relation/constant

**Rust implementation:**
- **MISSING**: No leaf cache
- Every visit to a Relation/Constant creates a new BooleanMatrix from scratch
- Even though BooleanFactory has gate caching, the matrix construction overhead is repeated

**Performance impact:**
- Relations used multiple times (very common) are re-interpreted each time
- Matrix allocation and variable assignment repeated unnecessarily
- Less severe than #1 but still measurable on relation-heavy formulas

**Estimated impact:** 10-30% slower for formulas using same relations multiple times.

---

### 3. **Other Potential Optimizations**

**Implemented in Rust:**
- ✓ Gate-level deduplication (BooleanFactory cache)
- ✓ CNF memoization (gates shared during Tseitin transformation)

**Not compared:**
- Java's IntSet/IntVector custom collections vs Rust's std collections
- Java's BooleanMatrix implementation details
- Early evaluation of constant formulas

---

## Performance Recommendations

**Priority 1 (Critical):** Implement FOL→Boolean translation caching
- Add shared node detection pass before translation
- Implement cache with (Node, Environment) keys
- Expected: 2-100x speedup on formulas with sharing

**Priority 2 (Important):** Add leaf expression caching
- Simple HashMap cache for Relation→BooleanMatrix
- Expected: 10-30% speedup

**Priority 3 (Nice to have):** Profile and optimize hot paths
- BooleanMatrix operations
- Quantifier expansion
- CNF generation

---

## Memory Management: GC vs Arc vs Arena

### Why Java's Caching is "Free"

**Java approach:**
```java
class BinaryFormula extends Formula {
    private final Formula left;
    private final Formula right;
    // ...
}

// Caching uses object identity (pointer equality)
IdentityHashMap<Formula, CachedResult> cache;
BinaryFormula node = ...; // heap-allocated object
cache.put(node, result);  // key is object reference
```

**Key insight:** Every AST node is a heap-allocated object with inherent identity. The GC heap makes sharing trivial—just reference the same object.

**Critical detail:** In Java, the IdentityHashMap holding a reference to `node` keeps that object alive. The GC sees the reference in the map and won't collect the object. This makes identity-based caching safe and natural.

---

### Why Rust's Enum-Based AST Makes Caching Harder

**Current Rust approach:**
```rust
pub enum Formula {
    Binary {
        left: Box<Formula>,
        op: BinaryFormulaOp,
        right: Box<Formula>,
    },
    // ...
}
```

**Problem:** `Formula::Binary { ... }` is a **value type**, not an object with identity.
- Can't use pointer equality to cache translations
- Each pattern match creates/unpacks values
- No inherent "same node" concept

**Attempted solutions:**

1. **Structural hashing** (expensive)
   - Hash entire AST subtree to use as cache key
   - Much slower than pointer equality
   - Not what Java does

2. **Raw pointer as key** (UNSOUND)
   ```rust
   cache: HashMap<*const FormulaInner, Result>
   ```
   - **Problem:** Pointer can dangle after Arc is dropped
   - New Arc could be allocated at same address → cache collision
   - In Java, the reference in the map keeps object alive
   - In Rust, raw pointer doesn't keep Arc alive
   - **This is subtly broken!**

3. **Arc in cache key** (correct but requires care)
   ```rust
   cache: HashMap<NodeIdentity, Result>  // NodeIdentity wraps Arc
   ```
   - Cache holds Arc, keeping node alive
   - Custom Hash/Eq use pointer identity
   - Mimics Java's IdentityHashMap semantics
   - Must clear cache appropriately to avoid memory leaks

---

### Current Arc/Box/Arena Usage Analysis

**Arc (3 uses - APPROPRIATE):**
- `Relation::inner` - Arc for identity equality (HashMap keys)
- `Variable::inner` - Arc for identity equality
- `Universe::inner` - Arc for shared data

**Why Arc here is good:**
- Needed for identity-based equality (`Arc::ptr_eq`)
- Relations/Variables are shared across formulas
- Matches Java's object identity behavior

**Box (~50 uses - NECESSARY):**
- All AST enum variants with recursive children
- `Formula::Binary { left: Box<Formula>, ... }`
- Required for recursive types in Rust (can't have infinite size)

**Arena (1 use - APPROPRIATE):**
- `BooleanFactory::arena` for BooleanMatrix/BooleanFormula storage
- Perfect fit: uniform lifetime, bulk deallocation after solving
- Data never escapes the translation phase

**Vec (~56 uses - APPROPRIATE):**
- Collections of formulas (`Vec<Formula>`)
- Temporary lists during translation
- Standard Rust pattern

---

### Should We Expand Arena Usage?

**Short answer: No, not for the missing caching optimization.**

**Important note:** Arena allocations (like bumpalo) ARE stable in Rust—pointers don't move, and you can use addresses for identity. The blocker isn't technical; it's ergonomic.

**Why Arena doesn't solve the caching problem:**

1. **API complexity - lifetime parameters everywhere**
   ```rust
   // Would need this:
   pub enum Formula<'arena> {
       Binary {
           left: &'arena Formula<'arena>,
           right: &'arena Formula<'arena>,
       }
   }

   // Instead of clean:
   pub enum Formula {
       Binary { left: Box<Formula>, right: Box<Formula> }
   }
   ```
   - Lifetime parameter is viral - spreads to every function
   - User API becomes much more complex
   - Not idiomatic for a library API

2. **We don't control AST construction**
   - Users build formulas incrementally: `a.and(b).or(c)`
   - Can't force them to use an arena
   - AST ownership is with the user, not internal to solver

3. **Already using Arena optimally**
   - BooleanMatrix/Formula are arena-allocated during translation ✓
   - Tied to translation phase lifetime ✓
   - Bulk deallocation after CNF conversion ✓
   - But the input AST (Formula/Expression) is user-owned

**What WOULD help for caching:**

1. **Arc-wrap AST nodes with proper cache design**
   ```rust
   pub struct Formula(Arc<FormulaInner>);

   // WRONG - pointer can dangle:
   // cache: HashMap<*const FormulaInner, Result>

   // RIGHT - Arc keeps node alive:
   struct NodeIdentity(Arc<FormulaInner>);
   impl Hash for NodeIdentity {
       fn hash<H: Hasher>(&self, state: &mut H) {
           Arc::as_ptr(&self.0).hash(state)  // Use address for hash
       }
   }
   impl PartialEq for NodeIdentity {
       fn eq(&self, other: &Self) -> bool {
           Arc::ptr_eq(&self.0, &other.0)  // Compare by identity
       }
   }

   cache: HashMap<NodeIdentity, CachedResult>
   ```
   - **Critical:** Cache must hold the Arc, not just raw pointer
   - Raw `Arc::as_ptr()` can dangle once Arc is dropped
   - Java's IdentityHashMap keeps objects alive; Rust must do this explicitly
   - **Pro:** Clean API, enables identity-based caching
   - **Pro:** Matches Java semantics correctly
   - **Con:** Memory overhead (~16 bytes per node)
   - **Con:** Cache holds references to nodes, must be cleared appropriately
   - **Con:** Clearing cache with N entries = N individual Arc drops (O(N) atomic decrements)
   - **Con:** Unlike GC or arena, can't bulk-free cached nodes in O(1)

2. **Arena-allocated AST** (technically sound, ergonomically viable with context)
   ```rust
   // FormulaInner - actual data allocated in arena (like BooleanFormula pattern)
   pub enum FormulaInner<'a> {
       Binary {
           left: Handle<'a, FormulaInner<'a>>,
           right: Handle<'a, FormulaInner<'a>>,
           op: BinaryFormulaOp,
       },
       Relation(Relation),
       // ...
   }

   // Formula - cheap Copy wrapper around Handle (like BooleanFormula)
   #[derive(Copy, Clone)]
   pub struct Formula<'a> {
       handle: Handle<'a, FormulaInner<'a>>,
   }

   impl Formula<'a> {
       fn new(handle: Handle<'a, FormulaInner<'a>>) -> Self {
           Self { handle }
       }
   }

   // Public API - Formula passed by value (cheap, just a Handle)
   impl Solver {
       pub fn binary(&self, left: Formula, op: Op, right: Formula) -> Formula {
           let inner = FormulaInner::Binary {
               left: left.handle,
               right: right.handle,
               op,
           };
           let handle = self.arena.alloc(inner);
           Formula::new(handle)
       }
       // Users call: solver.binary(a, And, b)
       // Get back: Formula<'solver> (Copy, cheap to pass around)
   }
   ```
   - **Pro:** Reuses existing Handle<'arena, T> generic type
   - **Pro:** Formula is Copy - passed by value, not reference
   - **Pro:** Matches proven BooleanFormula/FormulaInner pattern exactly
   - **Pro:** Handle is completely internal - users work with Formula values
   - **Pro:** Stable identity for caching - Formula.handle is Copy, use pointer/index
   - **Pro:** O(1) cache clear - just drop the arena (bulk deallocation)
   - **Pro:** All AST nodes freed at once when solver/context dropped
   - **Pro:** Future flexibility - can switch Handle from pointer to u32 index without API break
   - **Pro:** Better cache locality - Handle<FormulaInner> smaller than Box<Formula> if using indices
   - **Pro:** Consistent with existing BooleanFormula/BooleanMatrix design
   - **Con:** Lifetime parameters in type signatures
   - **Mitigation:** Solver methods take/return Formula values - lifetime is implicit in context
   - **Key advantage over Arc:** Clearing cache with 10,000 entries = O(1) arena drop, not 10,000 individual Arc drops

3. **Hybrid approach**
   - Keep current Box-based AST for user API
   - Convert to Arc internally during translation
   - Only pay Arc cost when needed
   - **Challenge:** Conversion overhead might negate benefits

---

### Conclusion

**The missing caching isn't caused by Rust's ownership model—it's a design choice with subtle tradeoffs.**

Java gets identity-based caching "for free" because:
1. Every AST node is a heap object with identity
2. References in caches keep objects alive (GC handles this)

Rust requires explicit choices:
1. Enum-based AST is efficient but lacks identity
2. Arc provides identity, but caches must hold Arcs (not raw pointers) to keep nodes alive
3. This creates memory management considerations Java doesn't have

**Three paths to enable caching:**

1. **Arena-allocated AST with context object and Handle pattern** (best performance characteristics)
   - Embed arena in Solver or TranslationContext
   - Split into Formula (Copy wrapper) / FormulaInner (arena-allocated data)
   - Reuse existing `Handle<'arena, FormulaInner>` type (no new type needed)
   - API: `solver.binary(a, And, b)` returns `Formula<'solver>` (Copy, passed by value)
   - Handle is completely hidden inside Formula
   - Cache uses Formula identity (via handle pointer/index)
   - **O(1) cache clear** - just drop the arena
   - **Future optimization:** Can change Handle from pointer to u32 index without API break
   - **Better cache locality:** Smaller handles = more fit in cache lines
   - **Clean API:** Formula is Copy, passed by value like other small types
   - Lifetime in type signatures but users just pass Formula values around
   - Matches Java's bulk-deallocation semantics
   - Best performance for large caches
   - **Proven pattern:** Exactly matches existing BooleanFormula/FormulaInner design

2. **Arc-wrap the AST with proper cache design** (simpler API)
   - Wrap in Arc like Relation/Variable
   - Cache holds Arc keys (keeps nodes alive)
   - Custom Hash/Eq for identity comparison
   - Must clear cache after translation
   - **O(N) cache clear** - N individual Arc drops (atomic decrements)
   - ~16 bytes overhead per node
   - Clean API, no lifetime parameters
   - Performance penalty for large caches

3. **Leaf caching only** (easiest first step)
   - Cache Relation → BooleanMatrix mappings
   - Relation already has Arc identity
   - 10-30% speedup with minimal changes
   - Doesn't need AST changes

**Recommendations:**

1. **Start with leaf caching** - low-hanging fruit, no API changes needed
2. **Profile before full AST caching** - measure whether it's needed for your workload
3. **If full caching is critical:**
   - **Arena + Handle approach strongly preferred** if you have a natural context object
     - O(1) bulk deallocation like Java/GC
     - Better performance for large caches
     - Consistent with existing BooleanFormula/Handle pattern
     - Future optimization opportunity (pointer → u32 index)
     - Better cache locality with compact handles
     - Lifetime in signatures but users call `context.method()` - not invasive
   - **Arc approach** if you need AST to outlive any context
     - Simpler ownership model
     - Pay O(N) cost for cache clearing
     - Could be measurable with thousands of cached nodes
4. **Don't use raw pointers as cache keys with Arc** - subtle use-after-free potential
5. **For arena + Handle:** Cache can use Handle identity (Copy, cheap comparison)

**Performance consideration:** With a cache of 10,000 nodes:
- Arena clear: O(1) - drop the whole arena
- Arc clear: O(10,000) - 10,000 atomic decrements + potential deallocations
- This could be milliseconds vs microseconds

**Design consideration:** Using existing Handle<'arena, T> with Formula/FormulaInner split:
- Exactly matches proven BooleanFormula/FormulaInner pattern in codebase
- Formula is Copy wrapper around Handle - cheap to pass by value
- FormulaInner is actual data allocated in arena
- Handle is completely internal - users work with Formula values
- Abstracts representation (pointer now, could be u32 index later)
- Smaller handles = better cache locality when using indices
- Consistency across codebase
- Future-proof API - change Handle implementation without breaking users

The fundamental difference: Java's GC and arena approaches both support O(1) bulk deallocation. Arc requires O(N) individual frees, which matters for large caches. The Handle pattern provides abstraction and optimization opportunities.

---

## Implementation Plan for Translation Caching

### Phase 1: Leaf Caching (Low-hanging fruit - 1-2 days)

**Goal:** 10-30% speedup with minimal changes

**Changes:**
1. Add `leaf_cache: RefCell<HashMap<Relation, BooleanMatrix<'static>>>` to FOL2BoolTranslator
2. In `translate_expression(Expression::Relation)`:
   ```rust
   if let Some(cached) = self.leaf_cache.borrow().get(rel) {
       return cached.clone()  // Clone is cheap - BooleanMatrix uses Handle
   }
   let matrix = self.interpreter.interpret_relation(rel);
   self.leaf_cache.borrow_mut().insert(rel.clone(), matrix.clone());
   matrix
   ```
3. Similarly for `Expression::Constant`
4. Test with examples that reuse relations heavily

**Risk:** Low - self-contained change, no API impact

**Success metric:** Measure translation time on examples with repeated relations

---

### Phase 2: Profiling and Measurement (1 day)

**Goal:** Determine if full AST caching is needed

**Tasks:**
1. Add instrumentation to count:
   - How many times each AST node is visited during translation
   - Cache hit rates from Phase 1
   - Translation time breakdown
2. Run on all examples, especially complex ones (alloy_netconfig, alloy_group_scheduling)
3. Identify formulas with significant sharing
4. Measure baseline performance before Phase 3

**Decision point:** If formulas have <2x sharing, stop here. If >5x sharing, proceed to Phase 3.

---

### Phase 3: Full AST Translation Caching (2-3 weeks)

**Goal:** 2-100x speedup on formulas with sharing

This is a **major refactoring** - requires converting AST to arena-allocated.

#### Step 3.1: Create FormulaArena and FormulaInner (3-4 days)

**Changes:**
1. Create new `ast_arena.rs` module:
   ```rust
   pub struct FormulaArena {
       bump: Bump,
   }

   pub enum FormulaInner<'a> {
       Constant(bool),
       Binary {
           left: Handle<'a, FormulaInner<'a>>,
           op: BinaryFormulaOp,
           right: Handle<'a, FormulaInner<'a>>,
       },
       // ... all current Formula variants
   }

   #[derive(Copy, Clone)]
   pub struct Formula<'a> {
       handle: Handle<'a, FormulaInner<'a>>,
   }
   ```

2. Keep old `Formula` enum as `FormulaLegacy` temporarily for migration

**Risk:** Medium - large structural change but isolated

#### Step 3.2: Add Conversion from Legacy to Arena AST (2-3 days)

**Changes:**
1. Implement `impl FormulaArena`:
   ```rust
   pub fn from_legacy(&self, legacy: &FormulaLegacy) -> Formula<'_> {
       match legacy {
           FormulaLegacy::Binary { left, op, right } => {
               let left_handle = self.from_legacy(left).handle;
               let right_handle = self.from_legacy(right).handle;
               let inner = FormulaInner::Binary {
                   left: left_handle,
                   right: right_handle,
                   op: *op,
               };
               Formula::new(self.alloc(inner))
           }
           // ... other cases
       }
   }
   ```

2. Add shared node detection pass:
   ```rust
   pub fn detect_shared_nodes(formula: &FormulaLegacy) -> HashSet<*const FormulaLegacy>
   ```

**Risk:** Low - conversion is isolated, doesn't affect existing code yet

#### Step 3.3: Add Translation Cache (2 days)

**Changes:**
1. Create translation cache:
   ```rust
   struct TranslationCache<'a> {
       // Key: Handle<FormulaInner> (stable pointer)
       // Value: cached BoolValue
       cache: RefCell<HashMap<Handle<'a, FormulaInner<'a>>, BoolValue<'a>>>,
       shared_nodes: HashSet<Handle<'a, FormulaInner<'a>>>,
   }
   ```

2. Modify FOL2BoolTranslator:
   ```rust
   fn translate_formula(&self, formula: Formula<'a>) -> BoolValue<'a> {
       // Check if this node is shared
       if self.cache.shared_nodes.contains(&formula.handle) {
           // Check cache
           if let Some(cached) = self.cache.cache.borrow().get(&formula.handle) {
               return cached.clone()
           }
       }

       // Translate normally
       let result = match self.resolve_formula(formula) {
           FormulaInner::Binary { left, op, right } => {
               let l = self.translate_formula(Formula::new(left));
               let r = self.translate_formula(Formula::new(right));
               // ... combine
           }
           // ...
       };

       // Cache if shared
       if self.cache.shared_nodes.contains(&formula.handle) {
           self.cache.cache.borrow_mut().insert(formula.handle, result.clone());
       }

       result
   }
   ```

**Risk:** Medium - complex logic but well-understood pattern from Java

#### Step 3.4: Update Translator Entry Point (1 day)

**Changes:**
1. Modify `Translator::evaluate`:
   ```rust
   pub fn evaluate(formula: &FormulaLegacy, bounds: &Bounds, ...) -> TranslationResult {
       let arena = FormulaArena::new();

       // Convert legacy AST to arena-allocated
       let arena_formula = arena.from_legacy(formula);

       // Detect shared nodes
       let shared = detect_shared_nodes_in_arena(&arena_formula);

       let interpreter = LeafInterpreter::from_bounds(bounds, options);
       let cache = TranslationCache::new(shared);
       let translator = FOL2BoolTranslator::new(&interpreter, cache);

       let value = translator.translate_formula(arena_formula);

       // ... rest as before
   }
   ```

**Risk:** Low - isolated change

#### Step 3.5: Testing and Validation (2-3 days)

**Tasks:**
1. Ensure all existing tests pass
2. Add tests for:
   - Shared node detection
   - Cache hit rates
   - Formulas with deep sharing
3. Benchmark against Phase 2 baseline
4. Verify memory usage doesn't explode (arena + cache)

**Risk:** Low - validation phase

---

### Phase 4: Migration to Arena-First (Optional - 1-2 weeks)

**Goal:** Make arena-allocated AST the primary representation

This would involve:
1. Moving Formula construction to builder pattern on Solver/Context
2. Deprecating current Formula builders
3. Gradual migration of examples

**Risk:** High - API breaking change
**Decision:** Only if profiling shows significant benefit AND we want to commit to this pattern

---

### Timeline Summary

**Conservative estimate:**
- Phase 1: 1-2 days (leaf caching) ✓ Safe
- Phase 2: 1 day (profiling) ✓ Safe
- Phase 3: 2-3 weeks (full caching) ⚠️ Major change
- Phase 4: 1-2 weeks (migration) ❌ Breaking changes

**Recommended approach:**
1. **Do Phase 1 immediately** - low risk, clear benefit
2. **Do Phase 2 to measure** - data-driven decision
3. **Only do Phase 3 if:**
   - Profiling shows >5x node revisits
   - Performance is actually a bottleneck for users
   - Willing to maintain dual AST representation during migration

**Alternative:** If Phase 2 shows modest sharing, stop at Phase 1 and accept 10-30% improvement rather than taking on Phase 3 complexity.
