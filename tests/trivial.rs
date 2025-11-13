//! Trivial solver tests - boolean formulas

use kodkod_rs::ast::Formula;
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_true_is_sat() {
    let universe = Universe::new(&["A"]).unwrap();
    let bounds = Bounds::new(universe);
    let solver = Solver::new(Options::default());

    let solution = solver.solve(&Formula::TRUE, &bounds).unwrap();
    assert!(solution.is_sat(), "TRUE should be SAT");
}

#[test]
fn test_false_is_unsat() {
    let universe = Universe::new(&["A"]).unwrap();
    let bounds = Bounds::new(universe);
    let solver = Solver::new(Options::default());

    let solution = solver.solve(&Formula::FALSE, &bounds).unwrap();
    assert!(solution.is_unsat(), "FALSE should be UNSAT");
}

#[test]
fn test_true_and_false_is_unsat() {
    let universe = Universe::new(&["A"]).unwrap();
    let bounds = Bounds::new(universe);
    let solver = Solver::new(Options::default());

    let formula = Formula::and(Formula::TRUE, Formula::FALSE);
    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_unsat(), "TRUE AND FALSE should be UNSAT");
}

#[test]
fn test_true_or_false_is_sat() {
    let universe = Universe::new(&["A"]).unwrap();
    let bounds = Bounds::new(universe);
    let solver = Solver::new(Options::default());

    let formula = Formula::or(Formula::TRUE, Formula::FALSE);
    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "TRUE OR FALSE should be SAT");
}
