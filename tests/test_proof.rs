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
