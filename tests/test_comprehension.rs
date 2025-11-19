//! Tests for set comprehension translation
//!
//! Verifies that {decls | formula} correctly translates to boolean matrices.
//! Based on kodkod.test.unit.EvaluatorTest comprehension tests.

use kodkod_rs::ast::{Decl, Decls, Expression, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_unary_comprehension() {
    // {v: Person | no v.shaken}
    // Should return people who didn't shake anyone's hand
    let atoms = vec!["Alice", "Bob", "Carol"];
    let universe = Universe::new(&atoms).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let person = Relation::unary("Person");
    let shaken = Relation::binary("shaken");

    // Person = {Alice, Bob, Carol}
    let person_tuples: Vec<Vec<&str>> = atoms.iter().map(|&s| vec![s]).collect();
    let person_refs: Vec<&[&str]> = person_tuples.iter().map(|v| v.as_slice()).collect();
    let person_set = factory.tuple_set(&person_refs).unwrap();
    bounds.bound_exactly(&person, person_set.clone()).unwrap();

    // shaken = {(Alice, Bob), (Bob, Carol)}
    // So Alice shook Bob's hand, Bob shook Carol's hand
    // Carol didn't shake anyone's hand
    let shaken_tuples = vec![vec!["Alice", "Bob"], vec!["Bob", "Carol"]];
    let shaken_refs: Vec<&[&str]> = shaken_tuples.iter().map(|v| v.as_slice()).collect();
    let shaken_set = factory.tuple_set(&shaken_refs).unwrap();
    bounds.bound_exactly(&shaken, shaken_set).unwrap();

    // Formula: {v: Person | no v.shaken}
    let v = Variable::unary("v");
    let v_shaken = Expression::from(v.clone()).join(Expression::from(shaken.clone()));
    let formula = v_shaken.no();
    let comprehension = formula.comprehension(Decls::from(Decl::one_of(v, Expression::from(person.clone()))));

    // Expected: {Carol} because only Carol didn't shake anyone's hand
    let expected = factory.tuple_set(&[&["Carol"][..]]).unwrap();
    let expected_relation = Relation::unary("expected");
    bounds.bound_exactly(&expected_relation, expected).unwrap();

    let check_formula = comprehension.equals(Expression::from(expected_relation));

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&check_formula, &bounds).unwrap();

    assert!(solution.is_sat(), "Comprehension should correctly identify Carol as having no shaken hands");
}

#[test]
fn test_binary_comprehension() {
    // {v0, v1: Person | v1 in v0.shaken} should equal shaken
    let atoms = vec!["Alice", "Bob", "Carol"];
    let universe = Universe::new(&atoms).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let person = Relation::unary("Person");
    let shaken = Relation::binary("shaken");

    let person_tuples: Vec<Vec<&str>> = atoms.iter().map(|&s| vec![s]).collect();
    let person_refs: Vec<&[&str]> = person_tuples.iter().map(|v| v.as_slice()).collect();
    let person_set = factory.tuple_set(&person_refs).unwrap();
    bounds.bound_exactly(&person, person_set.clone()).unwrap();

    let shaken_tuples = vec![vec!["Alice", "Bob"], vec!["Bob", "Carol"]];
    let shaken_refs: Vec<&[&str]> = shaken_tuples.iter().map(|v| v.as_slice()).collect();
    let shaken_set = factory.tuple_set(&shaken_refs).unwrap();
    bounds.bound_exactly(&shaken, shaken_set).unwrap();

    // {v0, v1: Person | v1 in v0.shaken}
    let v0 = Variable::unary("v0");
    let v1 = Variable::unary("v1");

    let v0_shaken = Expression::from(v0.clone()).join(Expression::from(shaken.clone()));
    let formula = Expression::from(v1.clone()).in_set(v0_shaken);

    let decls = Decls::from(Decl::one_of(v0, Expression::from(person.clone())))
        .and(Decl::one_of(v1, Expression::from(person.clone())));
    let comprehension = formula.comprehension(decls);

    // The comprehension should equal shaken
    let check_formula = comprehension.equals(Expression::from(shaken));

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&check_formula, &bounds).unwrap();

    assert!(solution.is_sat(), "Binary comprehension should reconstruct the shaken relation");
}

#[test]
fn test_comprehension_with_constant() {
    // {v: Person | v = Alice} should be the singleton {Alice}
    let atoms = vec!["Alice", "Bob"];
    let universe = Universe::new(&atoms).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let person = Relation::unary("Person");
    let alice = Relation::unary("Alice");

    let person_tuples: Vec<Vec<&str>> = atoms.iter().map(|&s| vec![s]).collect();
    let person_refs: Vec<&[&str]> = person_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&person, factory.tuple_set(&person_refs).unwrap()).unwrap();
    bounds.bound_exactly(&alice, factory.tuple_set(&[&["Alice"][..]]).unwrap()).unwrap();

    // {v: Person | v = Alice}
    let v = Variable::unary("v");
    let formula = Expression::from(v.clone()).equals(Expression::from(alice.clone()));
    let comprehension = formula.comprehension(Decls::from(Decl::one_of(v, Expression::from(person))));

    // Should equal {Alice}
    let check_formula = comprehension.equals(Expression::from(alice));

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&check_formula, &bounds).unwrap();

    assert!(solution.is_sat(), "Comprehension with constant should create singleton");
}

#[test]
fn test_empty_comprehension() {
    // {v: Person | v != v} should be empty
    let atoms = vec!["Alice", "Bob"];
    let universe = Universe::new(&atoms).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let person = Relation::unary("Person");
    let person_tuples: Vec<Vec<&str>> = atoms.iter().map(|&s| vec![s]).collect();
    let person_refs: Vec<&[&str]> = person_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&person, factory.tuple_set(&person_refs).unwrap()).unwrap();

    // {v: Person | v != v} (always false)
    let v = Variable::unary("v");
    let formula = Expression::from(v.clone()).equals(Expression::from(v.clone())).not();
    let comprehension = formula.comprehension(Decls::from(Decl::one_of(v, Expression::from(person))));

    // Should be empty
    let check_formula = comprehension.no();

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&check_formula, &bounds).unwrap();

    assert!(solution.is_sat(), "Comprehension with contradictory formula should be empty");
}
