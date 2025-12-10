//! Tests for solution enumeration (solveAll)
//!
//! Following Java: kodkod.test.unit.EnumerationTest

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Helper to create a solver with symmetry breaking disabled
/// (symmetry breaking can eliminate valid solutions during enumeration)
fn solver_for_enumeration() -> Solver {
    let mut options = Options::default();
    options.symmetry_breaking = 0;
    Solver::new(options)
}

/// Simple test: enumerate all non-empty subsets of a 2-element set
#[test]
fn test_enumerate_subsets() {
    // Universe with 2 elements
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe);

    // Relation R can be any subset of {a, b}
    let r = Relation::unary("R");
    let factory = bounds.universe().factory();
    bounds
        .bound(&r, factory.none(1), factory.all(1))
        .unwrap();

    // Formula: R must be non-empty (generates real constraints)
    let r_expr: Expression = r.clone().into();
    let formula = r_expr.some();

    let solver = solver_for_enumeration();
    let mut solutions = Vec::new();
    for (i, sol_result) in solver.solve_all(&formula, &bounds).enumerate() {
        let sol = sol_result.unwrap();
        solutions.push(sol);
        if solutions.len() > 10 {
            panic!("Too many solutions at iteration {}", i);
        }
    }

    // Should have 3 SAT solutions ({a}, {b}, {a,b}) + 1 UNSAT at the end
    assert_eq!(solutions.len(), 4, "Expected 3 SAT + 1 UNSAT, got {}", solutions.len());

    // First 3 should be SAT
    for (i, sol) in solutions[..3].iter().enumerate() {
        assert!(sol.is_sat(), "Expected SAT solution at index {i}");
    }

    // Last should be UNSAT
    assert!(solutions[3].is_unsat(), "Expected UNSAT at end");
}

/// Test enumeration with a constraint
#[test]
fn test_enumerate_with_constraint() {
    // Universe with 3 elements
    let universe = Universe::new(&["a", "b", "c"]).unwrap();
    let mut bounds = Bounds::new(universe);

    // Relation R can be any subset of {a, b, c}
    let r = Relation::unary("R");
    let factory = bounds.universe().factory();
    bounds
        .bound(&r, factory.none(1), factory.all(1))
        .unwrap();

    // Formula: R must have exactly one element
    let r_expr: Expression = r.clone().into();
    let formula = r_expr.one();

    let solver = solver_for_enumeration();
    let solutions: Vec<_> = solver
        .solve_all(&formula, &bounds)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    // Should have 3 SAT solutions ({a}, {b}, {c}) + 1 UNSAT
    assert_eq!(solutions.len(), 4);

    // First 3 should be SAT with exactly one element
    for sol in &solutions[..3] {
        assert!(sol.is_sat());
        let instance = sol.instance().unwrap();
        let r_tuples = instance.tuples(&r).unwrap();
        assert_eq!(r_tuples.size(), 1, "R should have exactly one element");
    }

    // Last should be UNSAT
    assert!(solutions[3].is_unsat());
}

/// Test enumeration returns unique solutions
#[test]
fn test_enumerate_unique_solutions() {
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let r = Relation::unary("R");
    let factory = bounds.universe().factory();
    bounds
        .bound(&r, factory.none(1), factory.all(1))
        .unwrap();

    // Use a formula that requires R to be non-empty
    let r_expr: Expression = r.clone().into();
    let formula = r_expr.some();

    let solver = solver_for_enumeration();
    let solutions: Vec<_> = solver
        .solve_all(&formula, &bounds)
        .filter_map(|sol| sol.ok())
        .filter(|sol| sol.is_sat())
        .collect();

    // Collect the R tuples from each solution as sets
    let mut seen: std::collections::HashSet<Vec<String>> = std::collections::HashSet::new();
    for sol in &solutions {
        let instance = sol.instance().unwrap();
        let r_tuples = instance.tuples(&r).unwrap();
        let mut atoms: Vec<String> = r_tuples
            .iter()
            .map(|t| {
                kodkod_rs::instance::atom_as_str(t.atom(0).unwrap())
                    .unwrap()
                    .to_string()
            })
            .collect();
        atoms.sort();
        assert!(
            seen.insert(atoms.clone()),
            "Duplicate solution found: {:?}",
            atoms
        );
    }

    // Should have found 3 unique solutions ({a}, {b}, {a,b})
    assert_eq!(seen.len(), 3);
}

/// Test empty enumeration (unsatisfiable formula)
#[test]
fn test_enumerate_unsat() {
    let universe = Universe::new(&["a"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let r = Relation::unary("R");
    let factory = bounds.universe().factory();
    // R is exactly empty
    bounds.bound_exactly(&r, factory.none(1)).unwrap();

    // Formula: R must be non-empty (contradiction)
    let formula = Expression::from(r).some();

    let solver = solver_for_enumeration();
    let solutions: Vec<_> = solver
        .solve_all(&formula, &bounds)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    // Should have just 1 UNSAT (or trivially UNSAT)
    assert_eq!(solutions.len(), 1);
    assert!(!solutions[0].is_sat());
}

/// Test binary relation enumeration
#[test]
fn test_enumerate_binary_relation() {
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe);

    // Binary relation R with fixed domain, variable range
    let r = Relation::binary("R");
    let factory = bounds.universe().factory();

    // R is a partial function from a -> {a,b}
    // Lower: empty, Upper: {(a,a), (a,b)}
    let upper = factory.tuple_set(&[&["a", "a"], &["a", "b"]]).unwrap();
    bounds.bound(&r, factory.none(2), upper).unwrap();

    // Formula: R must be non-empty
    let r_expr: Expression = r.clone().into();
    let formula = r_expr.some();

    let solver = solver_for_enumeration();
    let sat_count = solver
        .solve_all(&formula, &bounds)
        .filter_map(|sol| sol.ok())
        .filter(|sol| sol.is_sat())
        .count();

    // 3 non-empty subsets: {(a,a)}, {(a,b)}, {(a,a),(a,b)}
    assert_eq!(sat_count, 3);
}
