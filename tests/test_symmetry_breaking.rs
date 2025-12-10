//! Tests for symmetry breaking with total orderings and acyclic relations
//!
//! Following Java: kodkod.test.unit.SymmetryBreakingTest
//!
//! These tests verify that symmetry breaking achieves the same variable reduction
//! as Java by using aggressive mode (directly modifying bounds).

use kodkod_rs::ast::{Expression, Formula, Relation, RelationPredicate};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Tests symmetry breaking with total ordering predicates
#[test]
fn test_total_ordering() {
    let atoms: Vec<String> = (0..10).map(|i| i.to_string()).collect();
    let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(&atom_strs).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let to1 = Relation::binary("to1");
    let ord1 = Relation::unary("ord1");
    let first1 = Relation::unary("first1");
    let last1 = Relation::unary("last1");

    let solver = Solver::new(Options::default());

    // Test 1: Basic total ordering
    let area_bound = factory.area(
        factory.tuple(&["0", "0"]).unwrap(),
        factory.tuple(&["4", "4"]).unwrap()
    ).unwrap();
    bounds.bound(&to1, factory.none(2), area_bound.clone()).unwrap();
    bounds
        .bound(&ord1, factory.none(1), factory.tuple_set(&[&["0"], &["1"], &["2"], &["3"], &["4"]]).unwrap())
        .unwrap();
    bounds
        .bound(&first1, factory.none(1), bounds.upper_bound(&ord1).unwrap().clone())
        .unwrap();
    bounds
        .bound(&last1, factory.none(1), bounds.upper_bound(&ord1).unwrap().clone())
        .unwrap();

    let ordered1 = Formula::relation_predicate(RelationPredicate::TotalOrdering {
        relation: to1.clone(),
        ordered: ord1.clone(),
        first: first1.clone(),
        last: last1.clone(),
    });

    let formula = Expression::from(to1.clone()).some().and(ordered1.clone());
    let sol = solver.solve(&formula, &bounds).unwrap();
    assert!(sol.is_sat(), "Expected SAT");

    // With aggressive symmetry breaking, total ordering should eliminate all primary variables
    // Java gets 0 primary vars by directly binding relations to constants
    let pvars = sol.statistics().primary_variables();
    println!("Total ordering: {} primary vars (Java expects 0)", pvars);
    assert_eq!(pvars, 0, "Expected Java parity: 0 primary variables with aggressive symmetry breaking");
}

/// Tests symmetry breaking with acyclic predicates  
#[test]
fn test_acyclic() {
    let atoms: Vec<String> = (0..10).map(|i| i.to_string()).collect();
    let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(&atom_strs).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let ac1 = Relation::binary("ac1");

    let solver = Solver::new(Options::default());

    // Test: Basic acyclic
    let area_bound = factory.area(
        factory.tuple(&["0", "0"]).unwrap(),
        factory.tuple(&["4", "4"]).unwrap()
    ).unwrap();
    bounds.bound(&ac1, factory.none(2), area_bound.clone()).unwrap();

    let formula = Expression::from(ac1.clone()).some().and(ac1.clone().acyclic());
    let sol = solver.solve(&formula, &bounds).unwrap();
    assert!(sol.is_sat());

    // With aggressive symmetry breaking, acyclic on 5x5 should give 10 primary vars
    // Java gets 10 vars by removing diagonal and one half of symmetric pairs
    let pvars = sol.statistics().primary_variables();
    println!("Acyclic: {} primary vars (Java expects 10)", pvars);
    assert_eq!(pvars, 10, "Expected Java parity: 10 primary variables for 5x5 acyclic");
}
