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

// ============================================================================
// Extended tests ported from Java EvaluatorTest using handshake example
// ============================================================================

use kodkod_rs::ast::{Decl, Decls, Variable};

/// Creates the handshake example instance from Java EvaluatorTest
fn setup_handshake() -> (Instance, Relation, Relation, Relation, Relation, Relation) {
    let universe = Universe::new(&[
        "Jocelyn_0", "Hilary_0", "Person_0", "Person_1", "Person_2",
        "Person_3", "Person_4", "Person_5", "Person_6", "Person_7"
    ]).unwrap();
    let factory = universe.factory();
    let mut instance = Instance::new(universe);

    let hilary = Relation::unary("hilary");
    let jocelyn = Relation::unary("jocelyn");
    let person = Relation::unary("person");
    let spouse = Relation::binary("spouse");
    let shaken = Relation::binary("shaken");

    instance.add(hilary.clone(), factory.tuple_set(&[&["Hilary_0"]]).unwrap()).unwrap();
    instance.add(jocelyn.clone(), factory.tuple_set(&[&["Jocelyn_0"]]).unwrap()).unwrap();
    instance.add(person.clone(), factory.all(1)).unwrap();

    // Spouse pairs
    instance.add(spouse.clone(), factory.tuple_set(&[
        &["Jocelyn_0", "Hilary_0"],
        &["Hilary_0", "Jocelyn_0"],
        &["Person_0", "Person_1"],
        &["Person_1", "Person_0"],
        &["Person_2", "Person_3"],
        &["Person_3", "Person_2"],
        &["Person_4", "Person_5"],
        &["Person_5", "Person_4"],
        &["Person_6", "Person_7"],
        &["Person_7", "Person_6"],
    ]).unwrap()).unwrap();

    // Shaken hands
    instance.add(shaken.clone(), factory.tuple_set(&[
        &["Jocelyn_0", "Person_1"],
        &["Jocelyn_0", "Person_3"],
        &["Jocelyn_0", "Person_4"],
        &["Jocelyn_0", "Person_7"],
        &["Hilary_0", "Person_1"],
        &["Hilary_0", "Person_3"],
        &["Hilary_0", "Person_4"],
        &["Hilary_0", "Person_7"],
        &["Person_0", "Person_3"],
        &["Person_0", "Person_4"],
        &["Person_0", "Person_7"],
        &["Person_1", "Jocelyn_0"],
        &["Person_1", "Hilary_0"],
        &["Person_1", "Person_3"],
        &["Person_1", "Person_4"],
        &["Person_1", "Person_7"],
        &["Person_3", "Jocelyn_0"],
        &["Person_3", "Hilary_0"],
        &["Person_3", "Person_0"],
        &["Person_3", "Person_1"],
        &["Person_3", "Person_4"],
        &["Person_3", "Person_5"],
        &["Person_3", "Person_6"],
        &["Person_3", "Person_7"],
        &["Person_4", "Jocelyn_0"],
        &["Person_4", "Hilary_0"],
        &["Person_4", "Person_0"],
        &["Person_4", "Person_1"],
        &["Person_4", "Person_3"],
        &["Person_4", "Person_7"],
        &["Person_5", "Person_3"],
        &["Person_5", "Person_7"],
        &["Person_6", "Person_3"],
        &["Person_7", "Jocelyn_0"],
        &["Person_7", "Hilary_0"],
        &["Person_7", "Person_0"],
        &["Person_7", "Person_1"],
        &["Person_7", "Person_3"],
        &["Person_7", "Person_4"],
        &["Person_7", "Person_5"],
    ]).unwrap()).unwrap();

    (instance, hilary, jocelyn, person, spouse, shaken)
}

#[test]
fn test_eval_union() {
    let (instance, hilary, jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // Hilary + Hilary = Hilary
    let union = hilary_e.clone().union(hilary_e.clone());
    let result = evaluator.evaluate_expression(&union);
    assert_eq!(result.size(), 1);

    // Hilary + Jocelyn + Person = Person
    let union = hilary_e.clone().union(jocelyn_e.clone()).union(person_e.clone());
    let result = evaluator.evaluate_expression(&union);
    let person_val = evaluator.evaluate_expression(&person_e);
    assert_eq!(result.size(), person_val.size());

    // spouse + shaken = spouse + shaken (check size)
    let spouse_val = evaluator.evaluate_expression(&spouse_e.clone());
    let shaken_val = evaluator.evaluate_expression(&shaken_e.clone());
    let union = spouse_e.union(shaken_e);
    let result = evaluator.evaluate_expression(&union);
    // Union size should be at most sum (equal if disjoint)
    assert!(result.size() <= spouse_val.size() + shaken_val.size());
}

#[test]
fn test_eval_difference() {
    let (instance, hilary, jocelyn, _person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let jocelyn_e = Expression::from(jocelyn.clone());
    let hilary_e = Expression::from(hilary.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // Jocelyn - Jocelyn = {}
    let diff = jocelyn_e.clone().difference(jocelyn_e.clone());
    let result = evaluator.evaluate_expression(&diff);
    assert_eq!(result.size(), 0);

    // Hilary - Jocelyn = Hilary
    let diff = hilary_e.clone().difference(jocelyn_e);
    let result = evaluator.evaluate_expression(&diff);
    assert_eq!(result.size(), 1);

    // spouse + shaken - spouse = shaken
    let union = spouse_e.clone().union(shaken_e.clone());
    let diff = union.difference(spouse_e);
    let result = evaluator.evaluate_expression(&diff);
    let shaken_val = evaluator.evaluate_expression(&shaken_e);
    assert_eq!(result.size(), shaken_val.size());
}

#[test]
fn test_eval_join() {
    let (instance, hilary, jocelyn, person, spouse, _shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());

    // Hilary.spouse = Jocelyn
    let join = hilary_e.clone().join(spouse_e.clone());
    let result = evaluator.evaluate_expression(&join);
    let jocelyn_val = evaluator.evaluate_expression(&jocelyn_e);
    assert_eq!(result.size(), jocelyn_val.size());

    // spouse.spouse.Hilary = Hilary
    let join = spouse_e.clone().join(spouse_e.clone()).join(hilary_e.clone());
    let result = evaluator.evaluate_expression(&join);
    let hilary_val = evaluator.evaluate_expression(&hilary_e);
    assert_eq!(result.size(), hilary_val.size());

    // spouse.Person = all persons in the first column of spouse
    let join = spouse_e.join(person_e);
    let result = evaluator.evaluate_expression(&join);
    assert!(result.size() > 0);
}

#[test]
fn test_eval_product() {
    let (instance, hilary, jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // Hilary->Jocelyn = single tuple
    let prod = hilary_e.product(jocelyn_e);
    let result = evaluator.evaluate_expression(&prod);
    assert_eq!(result.size(), 1);
    assert_eq!(result.arity(), 2);

    // Person->(spouse->shaken) = (Person->spouse)->shaken (same size)
    let left = person_e.clone().product(spouse_e.clone().product(shaken_e.clone()));
    let right = person_e.product(spouse_e).product(shaken_e);
    let left_result = evaluator.evaluate_expression(&left);
    let right_result = evaluator.evaluate_expression(&right);
    assert_eq!(left_result.size(), right_result.size());
}

#[test]
fn test_eval_intersection() {
    let (instance, hilary, _jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // Hilary & Person = Hilary
    let inter = hilary_e.clone().intersection(person_e.clone());
    let result = evaluator.evaluate_expression(&inter);
    let hilary_val = evaluator.evaluate_expression(&hilary_e);
    assert_eq!(result.size(), hilary_val.size());

    // Hilary & Person = Person & Hilary
    let inter1 = hilary_e.clone().intersection(person_e.clone());
    let inter2 = person_e.intersection(hilary_e);
    let r1 = evaluator.evaluate_expression(&inter1);
    let r2 = evaluator.evaluate_expression(&inter2);
    assert_eq!(r1.size(), r2.size());

    // spouse & shaken = {} (disjoint by construction)
    let inter = spouse_e.intersection(shaken_e);
    let result = evaluator.evaluate_expression(&inter);
    assert_eq!(result.size(), 0);
}

#[test]
fn test_eval_transpose() {
    let (instance, hilary, jocelyn, _person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // ~spouse = spouse (symmetric relation)
    let trans = spouse_e.clone().transpose();
    let result = evaluator.evaluate_expression(&trans);
    let spouse_val = evaluator.evaluate_expression(&spouse_e);
    assert_eq!(result.size(), spouse_val.size());

    // ~(Hilary->Jocelyn) = Jocelyn->Hilary
    let prod = hilary_e.product(jocelyn_e.clone());
    let trans = prod.transpose();
    let expected = jocelyn_e.product(Expression::from(hilary.clone()));
    let trans_result = evaluator.evaluate_expression(&trans);
    let expected_result = evaluator.evaluate_expression(&expected);
    assert_eq!(trans_result.size(), expected_result.size());

    // ~(~shaken) = shaken
    let double_trans = shaken_e.clone().transpose().transpose();
    let result = evaluator.evaluate_expression(&double_trans);
    let shaken_val = evaluator.evaluate_expression(&shaken_e);
    assert_eq!(result.size(), shaken_val.size());
}

#[test]
fn test_eval_subset() {
    let (instance, hilary, _jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // Hilary in Person = true
    let f = hilary_e.in_set(person_e.clone());
    assert!(evaluator.evaluate(&f));

    // shaken in spouse = false
    let f = shaken_e.in_set(spouse_e.clone());
    assert!(!evaluator.evaluate(&f));

    // spouse in Person->Person = true
    let f = spouse_e.in_set(person_e.clone().product(person_e));
    assert!(evaluator.evaluate(&f));
}

#[test]
fn test_eval_equals() {
    let (instance, hilary, jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // Person = Person
    let f = person_e.clone().equals(person_e);
    assert!(evaluator.evaluate(&f));

    // spouse = shaken = false
    let f = spouse_e.equals(shaken_e);
    assert!(!evaluator.evaluate(&f));

    // Hilary = Jocelyn = false
    let f = hilary_e.equals(jocelyn_e);
    assert!(!evaluator.evaluate(&f));
}

#[test]
fn test_eval_implies() {
    let (instance, hilary, jocelyn, person, _spouse, _shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let person_e = Expression::from(person.clone());

    // Hilary in Person => Jocelyn in Person = true
    let f = hilary_e.clone().in_set(person_e.clone())
        .implies(jocelyn_e.clone().in_set(person_e.clone()));
    assert!(evaluator.evaluate(&f));

    // Hilary in Person => Person in Jocelyn = false
    let f = hilary_e.clone().in_set(person_e.clone())
        .implies(person_e.clone().in_set(jocelyn_e.clone()));
    assert!(!evaluator.evaluate(&f));

    // false => anything = true
    let f = hilary_e.equals(jocelyn_e.clone())
        .implies(jocelyn_e.in_set(person_e));
    assert!(evaluator.evaluate(&f));
}

#[test]
fn test_eval_iff() {
    let (instance, hilary, jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let jocelyn_e = Expression::from(jocelyn.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    // (Hilary in Person) <=> (Jocelyn in Person) = true
    let f = hilary_e.clone().in_set(person_e.clone())
        .iff(jocelyn_e.clone().in_set(person_e.clone()));
    assert!(evaluator.evaluate(&f));

    // (Hilary = Jocelyn) <=> (spouse = shaken) = true (both false)
    let f = hilary_e.equals(jocelyn_e)
        .iff(spouse_e.equals(shaken_e));
    assert!(evaluator.evaluate(&f));
}

#[test]
fn test_eval_multiplicity_formula() {
    let (instance, hilary, _jocelyn, person, spouse, _shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let hilary_e = Expression::from(hilary.clone());
    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());

    // some Person = true
    assert!(evaluator.evaluate(&person_e.clone().some()));

    // some (Person - Person) = false
    let diff = person_e.clone().difference(person_e.clone());
    assert!(!evaluator.evaluate(&diff.clone().some()));

    // no Person = false
    assert!(!evaluator.evaluate(&person_e.clone().no()));

    // no (Person - Person) = true
    assert!(evaluator.evaluate(&diff.no()));

    // one Hilary = true
    assert!(evaluator.evaluate(&hilary_e.one()));

    // one spouse = false (multiple pairs)
    assert!(!evaluator.evaluate(&spouse_e.one()));

    // lone (Person - Person) = true
    let diff = person_e.clone().difference(person_e);
    assert!(evaluator.evaluate(&diff.lone()));
}

#[test]
fn test_eval_quantified_formula() {
    let (instance, _hilary, _jocelyn, person, spouse, shaken) = setup_handshake();
    let evaluator = Evaluator::new(&instance);

    let person_e = Expression::from(person.clone());
    let spouse_e = Expression::from(spouse.clone());
    let shaken_e = Expression::from(shaken.clone());

    let p = Variable::unary("p");
    let q = Variable::unary("q");
    let pdecl = Decl::one_of(p.clone(), person_e.clone());
    let qdecl = Decl::one_of(q.clone(), person_e.clone());

    // all p: Person | some p.spouse = true (everyone has a spouse)
    let body = Expression::from(p.clone()).join(spouse_e.clone()).some();
    let f = Formula::forall(Decls::from(pdecl.clone()), body);
    assert!(evaluator.evaluate(&f));

    // some p: Person | no p.shaken = true (someone hasn't shaken hands)
    let body = Expression::from(p.clone()).join(shaken_e.clone()).no();
    let f = Formula::exists(Decls::from(pdecl.clone()), body);
    assert!(evaluator.evaluate(&f));

    // some p, q: Person | !(p = q) && (p.shaken = q.shaken) = true
    let body = Expression::from(p.clone()).equals(Expression::from(q.clone())).not()
        .and(Expression::from(p).join(shaken_e.clone()).equals(Expression::from(q).join(shaken_e)));
    let f = Formula::exists(Decls::from(pdecl).and(qdecl), body);
    assert!(evaluator.evaluate(&f));
}
