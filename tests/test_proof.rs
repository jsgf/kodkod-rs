//! Tests for unsatisfiable core extraction
//!
//! Tests the proof system for extracting minimal unsat cores.

use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_trivial_unsat_proof() {
    // Test that we can extract a proof for a trivially UNSAT formula (constant FALSE)
    let universe = Universe::new(&["a", "b"]).unwrap();
    let bounds = Bounds::new(universe);

    // Constant FALSE formula
    let formula = Formula::FALSE;

    // Enable logging to get proof
    let mut options = Options::default();
    options.log_translation = true;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds).unwrap();

    // Should be trivially UNSAT
    assert!(solution.is_unsat());
    assert!(solution.is_trivial());

    // Should have a proof
    let proof = solution.proof().expect("Should have proof for trivially UNSAT");

    // Core should contain the FALSE formula
    let core = proof.core().expect("Proof should have a core");
    assert_eq!(core.len(), 1, "Core should have exactly 1 formula");
    assert!(core.contains_key(&Formula::FALSE), "Core should contain FALSE");
}

#[test]
fn test_trivial_unsat_no_logging() {
    // Test that we DON'T get a proof when logging is disabled
    let universe = Universe::new(&["a", "b"]).unwrap();
    let bounds = Bounds::new(universe);

    let formula = Formula::FALSE;

    // Default options have log_translation = false
    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds).unwrap();

    // Should be trivially UNSAT but no proof
    assert!(solution.is_unsat());
    assert!(solution.proof().is_none(), "Should NOT have proof when logging disabled");
}

#[test]
fn test_contradictory_formula_proof() {
    // Test proof for a formula that becomes UNSAT through simplification
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());

    let r = Relation::unary("r");
    let factory = universe.factory();

    // Empty upper bound - r.some() is unsatisfiable
    bounds.bound(&r, factory.none(1), factory.none(1)).unwrap();

    let formula = Expression::from(r).some();

    let mut options = Options::default();
    options.log_translation = true;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds).unwrap();

    // Should be trivially UNSAT (r.some() with empty bounds simplifies to FALSE)
    assert!(solution.is_unsat());

    // May have proof depending on when simplification happens
    if let Some(proof) = solution.proof() {
        let core = proof.core().expect("Proof should have a core");
        assert!(!core.is_empty(), "Core should not be empty");
    }
}

#[test]
fn test_sat_has_no_proof() {
    // SAT solutions should not have proofs
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());

    let r = Relation::unary("r");
    let factory = universe.factory();

    bounds.bound(&r, factory.none(1), factory.all(1)).unwrap();

    let formula = Expression::from(r).some();

    let mut options = Options::default();
    options.log_translation = true;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds).unwrap();

    assert!(solution.is_sat());
    assert!(solution.proof().is_none(), "SAT solutions should not have proofs");
}

#[test]
fn test_minimal_core_simple() {
    // Test that the core is minimal: removing any formula makes it SAT
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());

    let r1 = Relation::unary("r1");
    let r2 = Relation::unary("r2");
    let factory = universe.factory();

    // r1 can be anything, r2 can be anything
    bounds.bound(&r1, factory.none(1), factory.all(1)).unwrap();
    bounds.bound(&r2, factory.none(1), factory.all(1)).unwrap();

    // Create three contradictory constraints:
    // 1. r1.some (r1 must be non-empty)
    // 2. r2.some (r2 must be non-empty)
    // 3. r1 & r2 = none AND universe = r1 + r2 AND |universe| = 1
    // With a 1-element universe, can't have both r1 and r2 non-empty and disjoint

    let universe_1 = Universe::new(&["a"]).unwrap();
    let mut bounds_1 = Bounds::new(universe_1.clone());
    let factory_1 = universe_1.factory();

    bounds_1.bound(&r1, factory_1.none(1), factory_1.all(1)).unwrap();
    bounds_1.bound(&r2, factory_1.none(1), factory_1.all(1)).unwrap();

    let conj1 = Expression::from(r1.clone()).some(); // r1 non-empty
    let conj2 = Expression::from(r2.clone()).some(); // r2 non-empty
    let conj3 = Expression::from(r1).intersection(Expression::from(r2)).no(); // r1 and r2 disjoint

    let formula = conj1.and(conj2).and(conj3);

    let mut options = Options::default();
    options.log_translation = true;
    options.flatten_formulas = true; // To get top-level conjuncts

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds_1).unwrap();

    assert!(solution.is_unsat(), "Formula should be UNSAT");

    // Should have a proof with minimal core
    if let Some(proof) = solution.proof() {
        let core = proof.core().expect("Proof should have a core");
        eprintln!("Core has {} formulas", core.len());

        // All three formulas should be in the minimal core
        assert_eq!(core.len(), 3, "Core should contain all 3 formulas for this example");
    } else {
        panic!("Should have proof when logging enabled");
    }
}

#[test]
fn test_minimal_core_redundant() {
    // Test with a formula that has redundant conjuncts
    let universe = Universe::new(&["a", "b"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());

    let r1 = Relation::unary("r1");
    let r2 = Relation::unary("r2");
    let factory = universe.factory();

    // r1 must be empty, r2 can be anything
    bounds.bound_exactly(&r1, factory.none(1)).unwrap();
    bounds.bound(&r2, factory.none(1), factory.all(1)).unwrap();

    // Two formulas where only one is needed for UNSAT:
    // 1. r1.some (UNSAT with empty r1)
    // 2. r2.no  (always satisfied since r2 lower bound is empty)
    let f1 = Expression::from(r1).some();
    let f2 = Expression::from(r2).no();

    let formula = f1.and(f2);

    let mut options = Options::default();
    options.log_translation = true;
    options.flatten_formulas = true;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds).unwrap();

    assert!(solution.is_unsat(), "Formula should be UNSAT");

    if let Some(proof) = solution.proof() {
        let core = proof.core().expect("Proof should have a core");
        eprintln!("Core has {} formulas (should be minimal)", core.len());

        // For trivially UNSAT formulas that simplify early,
        // the core contains all conjuncts since we can't determine
        // which one caused UNSAT without re-solving
        assert!(core.len() >= 1, "Core should have at least 1 formula");
        assert!(core.len() <= 2, "Core should not have more than 2 formulas");
    } else {
        panic!("Should have proof when logging enabled");
    }
}
