# kodkod-rs

A Rust port of [Kodkod](https://github.com/emina/kodkod), a relational logic solver.

## About

Kodkod is a solver for first-order relational logic with finite models. It translates formulas in relational logic to boolean satisfiability (SAT) problems, solves them using an off-the-shelf SAT solver, and converts satisfying assignments back to models of the original formula.

This Rust port aims to:
- Provide functionally equivalent API in idiomatic Rust
- Match or exceed Java version performance
- Enable parallelism opportunities (portfolio solving, parallel translation)
- Eliminate JNI complexity by using pure Rust SAT solvers

## Current Status

🚧 **Work in Progress** - See [PLAN.md](PLAN.md) for detailed implementation roadmap.

## Architecture

```
AST (enums) → FOL2Bool → Boolean Circuits → CNF → SAT Solver (ratsat/varisat)
                  ↓                                        ↓
             Identity Cache                           Solution/Proof
```

## API Example

```rust
use kodkod::ast::{Relation, Expression, Formula};
use kodkod::instance::{Universe, Bounds};
use kodkod::engine::Solver;

// Create universe
let universe = Universe::new(&["A", "B", "C"]);

// Define relation
let person = Relation::unary("Person");

// Set bounds
let mut bounds = Bounds::new(universe);
let factory = bounds.universe().factory();
bounds.bound(&person,
    factory.none(1),
    factory.tuple_set(&[&["A"], &["B"]]));

// Create formula: some Person
let formula = Expression::from(person).some();

// Solve
let solver = Solver::new(Options::default());
let solution = solver.solve(&formula, &bounds)?;

if solution.is_sat() {
    let instance = solution.instance().unwrap();
    println!("Solution: {:?}", instance.tuples(&person));
}
```

## Building

```bash
cargo build
cargo test
```

## Implementation Phases

See [PLAN.md](PLAN.md) for the complete implementation plan. Summary:

1. **Phase 1-4:** AST types (enums for Expression, Formula, IntExpression)
2. **Phase 5:** Visitor infrastructure
3. **Phase 6:** Bounds & Instance types
4. **Phase 7:** Int collections
5. **Phase 8-9:** Boolean layer & circuit factory
6. **Phase 10-11:** FOL→Boolean→CNF translation
7. **Phase 12-13:** SAT solver integration
8. **Phase 14-15:** Core Solver API & incremental solving
9. **Phase 16:** Example ports & validation
10. **Phase 17:** Parallelism (optional)

Each phase is independently testable.

## Differences from Java Version

- **Idiomatic Rust:** `snake_case`, `Result<T, E>`, borrowing, `Option<T>`
- **Clean SAT interface:** Core defines `SATSolver` trait, no dependencies on specific solvers
- **Pluggable backends:** Users can implement trait for any SAT solver (rustsat adapters provided for tests)
- **Enum-based AST:** Better pattern matching than OOP hierarchy
- **Explicit lifetimes:** Arena-allocated nodes with clear ownership
- **Parallelism ready:** Thread-safe design from start

## License

MIT (matching original Kodkod)

## References

- [Original Kodkod](https://github.com/emina/kodkod)
- [Kodkod Paper](http://people.csail.mit.edu/emina/pubs/kodkod.tacas07.pdf)
- [Java API Documentation](http://emina.github.io/kodkod/doc/)
