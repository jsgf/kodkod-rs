# ListSynth Debugging Notes

## Issue Summary
The ListSynth example compiles and runs but produces UNSATISFIABLE with 0 variables and 1 clause (trivially UNSAT), instead of finding the correct synthesis hole value.

## Expected Behavior
According to commit message 819e565, the solver should find hole="nil" as the solution.

## Debugging Findings

### What Works
- `hole.one()` alone: SAT with 28 variables ✓
- `pre() + hole.one()`: SAT with 47 variables ✓
- `pre() + loop_guard() + hole.one()`: SAT with 49 variables ✓

### What Fails
- `pre() + loop_guard() + post_with() + hole.one()`: UNSAT with 0 variables ✗

This indicates the issue is specifically in how `post_with()` interacts with the custom `next3()` and `head0()` expressions.

## Key Differences from Java

### Java (with inheritance/polymorphism)
```java
class ListSynth extends ListEncoding {
    Expression next0() { /* override with hole */ }

    Formula synthSpec() {
        return Formula.and(
            pre(),        // calls base class
            loopGuard(),  // calls base class
            post(),       // calls base class - internally uses next3()/head0() which call next0()
            hole.one()
        );
    }
}
```

When `post()` calls `next3()`, which calls `next0()`, Java's polymorphism ensures the overridden `next0()` in ListSynth is used.

### Rust (with composition)
```rust
impl ListSynth {
    fn next0(&self) -> Expression { /* override with hole */ }

    // Must manually redefine all intermediate methods
    fn next1(&self) -> Expression { self.next0().override_with(...) }
    fn next2(&self) -> Expression { self.guard0().then_else(self.next1(), self.next0()) }
    fn next3(&self) -> Expression { self.next2().override_with(...) }

    fn synth_spec(&self) -> Formula {
        Formula::and_all(vec![
            self.encoding.pre(),
            self.encoding.loop_guard(),
            self.encoding.post_with(self.next3(), self.head0()), // pass custom expressions
            hole_constraint,
        ])
    }
}
```

The Rust version manually passes custom expressions to `post_with()`, but something in this approach causes the formula to become contradictory.

## Potential Root Causes

1. **Expression Evaluation Order**: The custom expressions are built once when `synth_spec()` is called, vs. Java which builds them during `post()` evaluation

2. **SSA Chain Propagation**: The commit message specifically mentions "how next0() override propagates through the SSA variable chain (next1, next2, next3, etc)"

3. **Formula Translation**: Something in how the Rust Kodkod implementation translates formulas with `then_else` and `override_with` may differ from Java

4. **Bounds Interaction**: The universe with syntax atoms ("nil", "\"head\"", etc.) may interact unexpectedly with the formula

## Next Steps

This bug requires investigation into:
- How `Formula.then_else()` is translated to CNF in the Rust implementation
- Whether there's a difference in how `Expression.override_with()` works
- Potential issues with how relations bound to exact values interact with derived expressions
- Comparison of CNF output between Java and Rust versions for a minimal test case

The issue is non-trivial and may require modifications to the core Kodkod formula translation system.
