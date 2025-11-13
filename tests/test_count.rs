//! Simple cardinality test

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn ground_cardinality_exact() {
    // Create a simple unary relation
    let items = Relation::unary("Items");

    // Universe with 3 items
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let factory = universe.factory();

    let mut bounds = Bounds::new(universe);

    // Items = {A, B}  (fixed, not variable)
    let items_tuples = vec![vec!["A"], vec!["B"]];
    let items_refs: Vec<&[&str]> = items_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&items, factory.tuple_set(&items_refs).unwrap()).unwrap();

    let solver = Solver::new(Options::default());

    // Test: Items.count() == 2
    let items_expr = Expression::from(items.clone());
    let items_count = items_expr.count();
    let formula = items_count.eq(kodkod_rs::ast::IntExpression::constant(2));

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "items.count() == 2 should be SAT");
}

#[test]
fn ground_cardinality_wrong() {
    // Create a simple unary relation
    let items = Relation::unary("Items");

    // Universe with 3 items
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let factory = universe.factory();

    let mut bounds = Bounds::new(universe);

    // Items = {A, B}  (fixed, not variable)
    let items_tuples = vec![vec!["A"], vec!["B"]];
    let items_refs: Vec<&[&str]> = items_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&items, factory.tuple_set(&items_refs).unwrap()).unwrap();

    let solver = Solver::new(Options::default());

    // Test: Items.count() == 3 (should be UNSAT)
    let items_expr = Expression::from(items.clone());
    let items_count = items_expr.count();
    let formula = items_count.eq(kodkod_rs::ast::IntExpression::constant(3));

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(!result.is_sat(), "items.count() == 3 should be UNSAT");
}
