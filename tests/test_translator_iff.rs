//! Translator tests for IFF (if and only if) formulas
//!
//! Following Java: kodkod.test.unit.TranslatorTest.testIFF
//! Tests that IFF formulas translate correctly

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_iff_basic() {
    // Following Java: some r11 && (r11 in r12 iff r12 in r11)
    // Tests that bidirectional subset relationships work
    let universe = Universe::new(&["0", "1", "2", "3", "4"]).unwrap();
    let factory = universe.factory();

    let r11 = Relation::unary("r11");
    let r12 = Relation::unary("r12");

    let mut bounds = Bounds::new(universe);

    // r11: range from 2 to 4
    let lower = factory.none(1);
    let upper = factory.range(
        factory.tuple(&["2"]).unwrap(),
        factory.tuple(&["4"]).unwrap()
    ).unwrap();
    bounds.bound(&r11, lower, upper).unwrap();

    // r12: exactly {4}
    let exact = factory.tuple_set(&[&["4"]]).unwrap();
    bounds.bound_exactly(&r12, exact).unwrap();

    let solver = Solver::new(Options::default());

    // some r11 && (r11 in r12 iff r12 in r11)
    let formula = Expression::from(r11.clone()).some()
        .and(
            Expression::from(r11.clone())
                .in_set(Expression::from(r12.clone()))
                .iff(Expression::from(r12.clone()).in_set(Expression::from(r11.clone())))
        );

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "IFF with mutual subset should be SAT");
}

#[test]
fn test_iff_with_contradiction() {
    // Following Java: some r11 && no r12 && (r11 in r12 iff r12 in r11)
    // Tests that IFF catches contradictions
    let universe = Universe::new(&["0", "1", "2", "3", "4"]).unwrap();
    let factory = universe.factory();

    let r11 = Relation::unary("r11");
    let r12 = Relation::unary("r12");

    let mut bounds = Bounds::new(universe);

    // r11: range from 2 to 4
    let lower = factory.none(1);
    let upper = factory.range(
        factory.tuple(&["2"]).unwrap(),
        factory.tuple(&["4"]).unwrap()
    ).unwrap();
    bounds.bound(&r11, lower, upper).unwrap();

    // r12: can be empty or singleton
    let lower = factory.none(1);
    let upper = factory.tuple_set(&[&["4"]]).unwrap();
    bounds.bound(&r12, lower, upper).unwrap();

    let solver = Solver::new(Options::default());

    // some r11 && no r12 && (r11 in r12 iff r12 in r11)
    // This should be UNSAT: if r12 is empty and r11 is non-empty,
    // then (r11 in r12) is false (non-empty not subset of empty)
    // but (r12 in r11) is true (empty subset of anything)
    // so IFF fails
    let formula = Expression::from(r11.clone()).some()
        .and(Expression::from(r12.clone()).no())
        .and(
            Expression::from(r11.clone())
                .in_set(Expression::from(r12.clone()))
                .iff(Expression::from(r12.clone()).in_set(Expression::from(r11.clone())))
        );

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(!result.is_sat(), "IFF with asymmetric subsets should be UNSAT");
}

#[test]
fn test_iff_symmetry() {
    // Test that A iff B is equivalent to B iff A
    let universe = Universe::new(&["0", "1", "2"]).unwrap();
    let factory = universe.factory();

    let r1 = Relation::unary("r1");
    let r2 = Relation::unary("r2");

    let mut bounds = Bounds::new(universe.clone());

    bounds.bound(&r1, factory.none(1), factory.all(1)).unwrap();
    bounds.bound(&r2, factory.none(1), factory.all(1)).unwrap();

    let solver = Solver::new(Options::default());

    // Create formula: (A in B) iff (B in A)
    let formula1 = Expression::from(r1.clone())
        .in_set(Expression::from(r2.clone()))
        .iff(Expression::from(r2.clone()).in_set(Expression::from(r1.clone())));

    // Create formula: (B in A) iff (A in B)
    let formula2 = Expression::from(r2.clone())
        .in_set(Expression::from(r1.clone()))
        .iff(Expression::from(r1.clone()).in_set(Expression::from(r2.clone())));

    // Both should be SAT and have the same meaning
    let result1 = solver.solve(&formula1, &bounds).unwrap();
    assert!(result1.is_sat(), "First IFF should be SAT");

    let result2 = solver.solve(&formula2, &bounds).unwrap();
    assert!(result2.is_sat(), "Second IFF (reversed) should be SAT");
}

#[test]
fn test_iff_with_equals() {
    // Test IFF with equals instead of subset
    let universe = Universe::new(&["0", "1", "2"]).unwrap();
    let factory = universe.factory();

    let r1 = Relation::unary("r1");
    let r2 = Relation::unary("r2");

    let mut bounds = Bounds::new(universe);

    bounds.bound(&r1, factory.none(1), factory.all(1)).unwrap();
    bounds.bound(&r2, factory.none(1), factory.all(1)).unwrap();

    let solver = Solver::new(Options::default());

    // (r1 = r2) iff (r2 = r1)  - should always be SAT
    let formula = Expression::from(r1.clone())
        .equals(Expression::from(r2.clone()))
        .iff(Expression::from(r2.clone()).equals(Expression::from(r1.clone())));

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "IFF with symmetric equals should be SAT");
}
