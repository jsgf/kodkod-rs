//! Tests for if-then-else expressions
//!
//! Following Java: Various tests from BooleanCircuitTest and integration tests

use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::instance::{Bounds, TupleSet, Universe};
use kodkod_rs::solver::{Options as SolverOptions, Solver};

/// Test Formula::then_else creates proper Expression::If variants
#[test]
fn test_formula_then_else() {
    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");
    let r3 = Relation::unary("R3");

    let cond = Expression::from(r1.clone()).some();
    let then_expr = Expression::from(r2.clone());
    let else_expr = Expression::from(r3.clone());

    // Create if-then-else expression
    let ite_expr = cond.then_else(then_expr.clone(), else_expr.clone());

    // Verify arity matches (both branches must have same arity)
    assert_eq!(ite_expr.arity(), 1);
}

/// Test that then_else panics on arity mismatch
#[test]
#[should_panic(expected = "Arity mismatch")]
fn test_then_else_arity_mismatch() {
    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");
    let r3 = Relation::binary("R3");

    let cond = Expression::from(r1).some();
    let then_expr = Expression::from(r2);
    let else_expr = Expression::from(r3);

    // This should panic due to arity mismatch
    let _ite_expr = cond.then_else(then_expr, else_expr);
}

/// Test if-then-else with TRUE condition evaluates to then branch
#[test]
fn test_ite_true_condition() {
    // Universe with 3 atoms
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    let factory = bounds.universe().factory();

    // R1 = {A, B}, R2 = {C}
    let r1_tuples = factory.tuple_set(&[&["A"], &["B"]]).unwrap();
    let r2_tuples = factory.tuple_set(&[&["C"]]).unwrap();
    bounds.bound_exactly(&r1, r1_tuples).unwrap();
    bounds.bound_exactly(&r2, r2_tuples).unwrap();

    // Formula: TRUE ? R1 : R2
    let ite_expr = Formula::TRUE.then_else(Expression::from(r1.clone()), Expression::from(r2.clone()));

    // The result should equal R1
    let formula = ite_expr.equals(r1.into());

    let solver = Solver::new(SolverOptions::default());
    let result = solver.solve(&formula, &bounds).unwrap();

    assert!(result.is_sat(), "TRUE ? R1 : R2 should equal R1");
}

/// Test if-then-else with FALSE condition evaluates to else branch
#[test]
fn test_ite_false_condition() {
    // Universe with 3 atoms
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    let factory = bounds.universe().factory();

    // R1 = {A, B}, R2 = {C}
    let r1_tuples = factory.tuple_set(&[&["A"], &["B"]]).unwrap();
    let r2_tuples = factory.tuple_set(&[&["C"]]).unwrap();
    bounds.bound_exactly(&r1, r1_tuples).unwrap();
    bounds.bound_exactly(&r2, r2_tuples).unwrap();

    // Formula: FALSE ? R1 : R2
    let ite_expr = Formula::FALSE.then_else(r1.into(), Expression::from(r2.clone()));

    // The result should equal R2
    let formula = ite_expr.equals(r2.into());

    let solver = Solver::new(SolverOptions::default());
    let result = solver.solve(&formula, &bounds).unwrap();

    assert!(result.is_sat(), "FALSE ? R1 : R2 should equal R2");
}

/// Test if-then-else with conditional formula
#[test]
fn test_ite_conditional() {
    // Universe with 3 atoms
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let p = Relation::unary("P");
    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    let factory = bounds.universe().factory();

    // P can be empty or {A}
    let p_upper = factory.tuple_set(&[&["A"]]).unwrap();
    let p_lower = TupleSet::empty(bounds.universe().clone(), 1);
    bounds.bound(&p, p_lower, p_upper).unwrap();

    // R1 = {B}, R2 = {C}
    let r1_tuples = factory.tuple_set(&[&["B"]]).unwrap();
    let r2_tuples = factory.tuple_set(&[&["C"]]).unwrap();
    bounds.bound_exactly(&r1, r1_tuples.clone()).unwrap();
    bounds.bound_exactly(&r2, r2_tuples.clone()).unwrap();

    // Result relation
    let result_rel = Relation::unary("Result");
    let result_upper = factory.tuple_set(&[&["B"], &["C"]]).unwrap();
    let result_lower = TupleSet::empty(bounds.universe().clone(), 1);
    bounds.bound(&result_rel, result_lower, result_upper).unwrap();

    // Formula: Result = (some P ? R1 : R2)
    let cond = Expression::from(p.clone()).some();
    let ite_expr = cond.then_else(r1.into(), r2.into());
    let formula = Expression::from(result_rel.clone()).equals(ite_expr);

    let solver = Solver::new(SolverOptions::default());
    let sat_result = solver.solve(&formula, &bounds).unwrap();

    assert!(sat_result.is_sat(), "Should be satisfiable");

    if let Some(instance) = sat_result.instance() {
        let p_value = instance.tuples(&p).unwrap();
        let result_value = instance.tuples(&result_rel).unwrap();

        if p_value.is_empty() {
            // P is empty, so condition is false, result should be R2 = {C}
            assert_eq!(result_value.size(), 1);
            let result_tuple = result_value.iter().next().unwrap();
            assert_eq!(result_tuple.atom(0), Some("C"));
        } else {
            // P is non-empty, so condition is true, result should be R1 = {B}
            assert_eq!(result_value.size(), 1);
            let result_tuple = result_value.iter().next().unwrap();
            assert_eq!(result_tuple.atom(0), Some("B"));
        }
    }
}

/// Test nested if-then-else expressions
#[test]
fn test_nested_ite() {
    // Universe with 4 atoms
    let universe = Universe::new(&["A", "B", "C", "D"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let p = Relation::unary("P");
    let q = Relation::unary("Q");
    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");
    let r3 = Relation::unary("R3");

    let factory = bounds.universe().factory();

    // Set up bounds
    bounds.bound(&p, TupleSet::empty(bounds.universe().clone(), 1), factory.tuple_set(&[&["A"]]).unwrap()).unwrap();
    bounds.bound(&q, TupleSet::empty(bounds.universe().clone(), 1), factory.tuple_set(&[&["B"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r1, factory.tuple_set(&[&["C"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r2, factory.tuple_set(&[&["D"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r3, factory.tuple_set(&[&["A"]]).unwrap()).unwrap();

    // Nested: some P ? R1 : (some Q ? R2 : R3)
    let q_cond = Expression::from(q).some();
    let inner_ite = q_cond.then_else(r2.into(), r3.into());
    let p_cond = Expression::from(p).some();
    let outer_ite = p_cond.then_else(r1.into(), inner_ite);

    // Should be satisfiable and produce valid results
    let formula = Formula::TRUE.and(outer_ite.some());

    let solver = Solver::new(SolverOptions::default());
    let result = solver.solve(&formula, &bounds).unwrap();

    assert!(result.is_sat(), "Nested ITE should be satisfiable");
}

/// Test if-then-else with binary relations
#[test]
fn test_ite_binary_relations() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let p = Relation::unary("P");
    let r1 = Relation::binary("R1");
    let r2 = Relation::binary("R2");

    let factory = bounds.universe().factory();

    bounds.bound(&p, TupleSet::empty(bounds.universe().clone(), 1), factory.tuple_set(&[&["A"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r1, factory.tuple_set(&[&["A", "B"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r2, factory.tuple_set(&[&["B", "C"]]).unwrap()).unwrap();

    // Formula: some (some P ? R1 : R2)
    let p_cond = Expression::from(p).some();
    let ite_expr = p_cond.then_else(r1.into(), r2.into());
    let formula = ite_expr.some();

    let solver = Solver::new(SolverOptions::default());
    let result = solver.solve(&formula, &bounds).unwrap();

    assert!(result.is_sat(), "Binary relation ITE should be satisfiable");
}

/// Test if-then-else with union operations
#[test]
fn test_ite_with_operations() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut bounds = Bounds::new(universe);

    let p = Relation::unary("P");
    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");
    let r3 = Relation::unary("R3");

    let factory = bounds.universe().factory();

    bounds.bound(&p, TupleSet::empty(bounds.universe().clone(), 1), factory.tuple_set(&[&["A"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r1, factory.tuple_set(&[&["A"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r2, factory.tuple_set(&[&["B"]]).unwrap()).unwrap();
    bounds.bound_exactly(&r3, factory.tuple_set(&[&["C"]]).unwrap()).unwrap();

    // Formula: ((some P ? R1 : R2) + R3).some
    let p_cond = Expression::from(p).some();
    let ite_expr = p_cond.then_else(r1.into(), r2.into());
    let union_expr = ite_expr.union(r3.into());
    let formula = union_expr.some();

    let solver = Solver::new(SolverOptions::default());
    let result = solver.solve(&formula, &bounds).unwrap();

    assert!(result.is_sat(), "ITE with union should be satisfiable");
}
