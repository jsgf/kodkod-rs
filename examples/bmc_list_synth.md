# ListSynth Debugging Notes

## ROOT CAUSE IDENTIFIED

### The Fundamental Issue: Universe Atom Types

**Java Kodkod:**
```java
Universe universe(int size) {
    ArrayList<Object> elts = new ArrayList<>();
    elts.add("l0");
    elts.add("n0"); elts.add("n1"); // ... strings
    elts.add("nil");
    elts.add(headStx);      // Adds the Relation OBJECT itself as an atom
    elts.add(nearNode0Stx); // Adds the Relation OBJECT itself as an atom
    // ...
    return new Universe(elts);
}

// Later in synthBounds():
b.bound(hole, t.setOf("nil", headStx, nearNode0Stx, midNode0Stx, farNode0Stx));
//                     ^^^^^ String   ^^^^^^^^^^^^^^ Relation objects
```

**Rust Kodkod:**
```rust
struct UniverseInner {
    atoms: Vec<String>,  // ❌ Only strings!
    indices: FxHashMap<String, usize>,
}

// In our port:
elts.push("nil");
elts.push("\"head\"");        // ❌ String representation, not the Relation!
elts.push("\"nearNode0\"");   // ❌ String representation, not the Relation!
```

### Why This Matters

In Java, Relations are first-class atoms:
1. `headStx` is both a **variable being bound** AND an **atom in the universe**
2. The `hole` can be assigned to the actual Relation object `nearNode0Stx`
3. When `hole.join(meaning())` executes, it performs a relational join with the actual Relation object
4. The meaning map contains entries like `(nearNode0Stx → nearNode0())` where the key is the Relation object

In Rust, we only have strings:
1. We use `"\"nearNode0\""` as a string representation
2. The semantic linking between the hole and the meaning map is broken
3. Formula simplification likely detects this inconsistency and makes it trivially UNSAT

### Java Verification

Running Java ListSynth with SAT4J solver:
```
************ SYNTHESIZE REVERSE REPAIR FOR 3 NODES ************
SATISFIABLE
primary variables: 12
"??" = [[nil]]  ← ✓ Correctly finds hole=nil
```

Running Rust ListSynth:
```
UNSATISFIABLE (no synthesis)
num_variables: 0, num_clauses: 1  ← Trivially UNSAT before SAT solver runs
```

## Solution Options

### Option 1: Enum-based Atoms (Recommended)
```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Atom {
    String(String),
    Relation(Relation),
    // Future: Integer(i32), CustomObject(Box<dyn AtomObject>), etc.
}

struct UniverseInner {
    atoms: Vec<Atom>,
    indices: FxHashMap<Atom, usize>,
}
```

**Pros:**
- Type-safe
- Fast equality/hashing
- No dynamic dispatch overhead
- Clear what types are supported

**Cons:**
- Need to update all Universe API callers
- Adding new atom types requires enum modification

### Option 2: Trait-based Atoms
```rust
pub trait AtomTrait: Debug + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn atom_eq(&self, other: &dyn AtomTrait) -> bool;
    fn atom_hash(&self, hasher: &mut dyn Hasher);
}

struct UniverseInner {
    atoms: Vec<Box<dyn AtomTrait>>,
    indices: FxHashMap</* custom wrapper */, usize>,
}
```

**Pros:**
- Extensible to any type implementing trait
- Matches Java's Object flexibility

**Cons:**
- More complex (downcasting, hashing wrappers)
- Performance overhead from dynamic dispatch
- Harder to debug

## Impact Assessment

This affects:
- **Universe creation** - API must accept `Atom` enum or `Box<dyn AtomTrait>`
- **TupleFactory** - Creating tuples from atoms
- **Bounds** - Setting bounds with atom references
- **All examples** - Universe construction calls

## Next Steps

1. Implement Atom enum (preferred for simplicity and performance)
2. Refactor Universe and TupleFactory
3. Update all call sites
4. Re-test ListSynth to verify it resolves the UNSAT bug
5. Update other examples as needed

## Previous Investigation Summary

Before finding root cause, we discovered and fixed:
- Universe mismatch (checker: 8 atoms, synth: 12 atoms) ✓ Fixed
- Duplicate bounds (setting then overriding) ✓ Fixed
- Custom expression building with composition vs inheritance ✓ Working

But formula remained trivially UNSAT because the fundamental semantic linking between Relations as atoms was broken.

