//! Simple integration test demonstrating kodkod-rs solver

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_simple_person_some() {
    // Create a universe with 3 atoms
    let universe = Universe::new(&["Alice", "Bob", "Charlie"])
        .expect("Failed to create universe");

    // Create a relation for "Person"
    let person = Relation::unary("Person");

    // Set up bounds
    let mut bounds = Bounds::new(universe.clone());
    let factory = bounds.universe().factory();

    // Person can be any subset of {Alice, Bob, Charlie}
    bounds.bound(
        &person,
        factory.none(1),
        factory.tuple_set(&[&["Alice"], &["Bob"], &["Charlie"]]).unwrap(),
    ).expect("Failed to bind");

    // Create formula: "some Person" (there exists at least one person)
    let formula = Expression::from(person.clone()).some();

    // Solve
    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds).expect("Solve failed");

    assert!(solution.is_sat(), "Formula should be satisfiable");

    let instance = solution.instance().expect("Should have instance");
    assert_eq!(instance.universe().size(), 3);

    // The Person relation should be non-empty
    let person_tuples = instance.get(&person).expect("Should have Person relation");
    assert!(!person_tuples.is_empty(), "Person should be non-empty");
}
