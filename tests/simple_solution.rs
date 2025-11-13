//! Test to verify solution extraction works correctly

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_solution_extraction_with_lower_bound() {
    // Create a simple universe
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());

    // Create a simple relation R
    let r = Relation::unary("R");
    let factory = bounds.universe().factory();

    // R can be any subset of {A, B, C}, but must contain at least A
    bounds.bound(
        &r,
        factory.tuple_set(&[&["A"]]).unwrap(),  // lower: must contain A
        factory.tuple_set(&[&["A"], &["B"], &["C"]]).unwrap(),  // upper: can contain A, B, C
    ).unwrap();

    // Formula: R must be non-empty (which is already satisfied by lower bound)
    let formula = Expression::from(r.clone()).some();

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds).unwrap();

    assert!(solution.is_sat(), "Should be SAT");

    let instance = solution.instance().expect("Should have instance");
    let r_tuples = instance.get(&r).expect("Should have R relation");

    // R must contain at least A (from lower bound)
    assert!(!r_tuples.is_empty(), "R should not be empty");

    // Check that A is in the solution
    let mut has_a = false;
    for tuple in r_tuples.iter() {
        let atoms: Vec<_> = tuple.atoms().collect();
        if atoms == vec!["A"] {
            has_a = true;
        }
    }
    assert!(has_a, "R must contain A (from lower bound)");
}
