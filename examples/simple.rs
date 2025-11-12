//! Simple example demonstrating kodkod-rs solver
//!
//! Solves a basic relational logic problem

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
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
        factory.none(1), // lower bound: empty
        factory
            .tuple_set(&[&["Alice"], &["Bob"], &["Charlie"]])
            .expect("Failed to create tuple set"), // upper bound: all atoms
    );

    // Create formula: "some Person" (there exists at least one person)
    let formula = Expression::from(person.clone()).some();

    // Solve
    let solver = Solver::new(Options::default());
    println!("Solving: some Person");

    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            if solution.is_sat() {
                println!("✓ SAT - Formula is satisfiable!");
                println!(
                    "  Translation time: {}ms",
                    solution.statistics().translation_time()
                );
                println!(
                    "  Solving time: {}ms",
                    solution.statistics().solving_time()
                );

                if let Some(instance) = solution.instance() {
                    println!("  Universe size: {}", instance.universe().size());
                }
            } else if solution.is_unsat() {
                println!("✗ UNSAT - Formula is unsatisfiable");
            } else {
                println!("○ TRIVIAL - Formula is trivially true/false");
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}
