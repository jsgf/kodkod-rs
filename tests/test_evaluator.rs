/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR IN CONNECTION WITH
 * THE SOFTWARE.
 */

//! Tests for Evaluator
//!
//! Following Java: kodkod.test.unit.EvaluatorTest (when ported)

use kodkod_rs::ast::{Expression, Formula, IntExpression, Relation};
use kodkod_rs::engine::Evaluator;
use kodkod_rs::instance::{atom_as_str, Instance, Universe};

#[test]
fn test_evaluate_formula_true() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r = Relation::unary("R");
    instance.add(r.clone(), factory.tuple_set(&[&["A"], &["B"]]).unwrap()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // R.some should be true
    let formula = Expression::from(r.clone()).some();
    assert!(evaluator.evaluate(&formula));

    // R.no should be false
    let formula = Expression::from(r).no();
    assert!(!evaluator.evaluate(&formula));
}

#[test]
fn test_evaluate_formula_false() {
    let universe = Universe::new(&["A", "B"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r = Relation::unary("R");
    instance.add(r.clone(), factory.none(1)).unwrap();

    let evaluator = Evaluator::new(&instance);

    // R.some should be false (R is empty)
    let formula = Expression::from(r.clone()).some();
    assert!(!evaluator.evaluate(&formula));

    // R.no should be true
    let formula = Expression::from(r).no();
    assert!(evaluator.evaluate(&formula));
}

#[test]
fn test_evaluate_expression() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r = Relation::unary("R");
    let tuples = factory.tuple_set(&[&["A"], &["C"]]).unwrap();
    instance.add(r.clone(), tuples.clone()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // Evaluate R should return {A, C}
    let result = evaluator.evaluate_expression(&Expression::from(r));
    assert_eq!(result.size(), 2);
    assert_eq!(result.arity(), 1);

    // Check that result equals the original tuples
    assert_eq!(result.iter().count(), 2);
    let atoms: Vec<_> = result
        .iter()
        .map(|t| atom_as_str(t.atom(0).unwrap()).unwrap())
        .collect();
    assert!(atoms.contains(&"A"));
    assert!(atoms.contains(&"C"));
}

#[test]
fn test_evaluate_expression_binary() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r = Relation::binary("R");
    let tuples = factory.tuple_set(&[&["A", "B"], &["B", "C"]]).unwrap();
    instance.add(r.clone(), tuples).unwrap();

    let evaluator = Evaluator::new(&instance);

    // Evaluate R should return {(A,B), (B,C)}
    let result = evaluator.evaluate_expression(&Expression::from(r));
    assert_eq!(result.size(), 2);
    assert_eq!(result.arity(), 2);
}

#[test]
fn test_evaluate_expression_union() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    instance.add(r1.clone(), factory.tuple_set(&[&["A"]]).unwrap()).unwrap();
    instance.add(r2.clone(), factory.tuple_set(&[&["B"]]).unwrap()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // Evaluate R1 + R2 should return {A, B}
    let expr = Expression::from(r1).union(Expression::from(r2));
    let result = evaluator.evaluate_expression(&expr);

    assert_eq!(result.size(), 2);
    let atoms: Vec<_> = result
        .iter()
        .map(|t| atom_as_str(t.atom(0).unwrap()).unwrap())
        .collect();
    assert!(atoms.contains(&"A"));
    assert!(atoms.contains(&"B"));
}

#[test]
fn test_evaluate_expression_intersection() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    instance.add(r1.clone(), factory.tuple_set(&[&["A"], &["B"]]).unwrap()).unwrap();
    instance.add(r2.clone(), factory.tuple_set(&[&["B"], &["C"]]).unwrap()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // Evaluate R1 & R2 should return {B}
    let expr = Expression::from(r1).intersection(Expression::from(r2));
    let result = evaluator.evaluate_expression(&expr);

    assert_eq!(result.size(), 1);
    assert_eq!(
        atom_as_str(result.iter().next().unwrap().atom(0).unwrap()),
        Some("B")
    );
}

#[test]
fn test_evaluate_int_expression() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r = Relation::unary("R");
    instance.add(r.clone(), factory.tuple_set(&[&["A"], &["B"]]).unwrap()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // Evaluate #R should return 2
    let int_expr = Expression::from(r).count();
    let result = evaluator.evaluate_int_expression(&int_expr);

    assert_eq!(result, 2);
}

#[test]
fn test_evaluate_int_expression_sum() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    instance.add(r1.clone(), factory.tuple_set(&[&["A"]]).unwrap()).unwrap();
    instance.add(r2.clone(), factory.tuple_set(&[&["B"], &["C"]]).unwrap()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // Evaluate #R1 + #R2 should return 3
    let int_expr = Expression::from(r1).count().plus(Expression::from(r2).count());
    let result = evaluator.evaluate_int_expression(&int_expr);

    assert_eq!(result, 3);
}

#[test]
fn test_evaluate_constant_formula() {
    let universe = Universe::new(&["A"]).unwrap();
    let instance = Instance::new(universe);

    let evaluator = Evaluator::new(&instance);

    // TRUE formula
    assert!(evaluator.evaluate(&Formula::constant(true)));

    // FALSE formula
    assert!(!evaluator.evaluate(&Formula::constant(false)));
}

#[test]
fn test_evaluate_complex_formula() {
    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let mut instance = Instance::new(universe.clone());
    let factory = universe.factory();

    let r1 = Relation::unary("R1");
    let r2 = Relation::unary("R2");

    instance.add(r1.clone(), factory.tuple_set(&[&["A"], &["B"]]).unwrap()).unwrap();
    instance.add(r2.clone(), factory.tuple_set(&[&["B"], &["C"]]).unwrap()).unwrap();

    let evaluator = Evaluator::new(&instance);

    // (some R1) && (some R2)
    let formula = Expression::from(r1.clone()).some()
        .and(Expression::from(r2.clone()).some());
    assert!(evaluator.evaluate(&formula));

    // (no R1) || (some R2)
    let formula = Expression::from(r1.clone()).no()
        .or(Expression::from(r2).some());
    assert!(evaluator.evaluate(&formula));

    // (no R1)
    let formula = Expression::from(r1).no();
    assert!(!evaluator.evaluate(&formula));
}
