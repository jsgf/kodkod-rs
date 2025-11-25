/*
 * Minimal test case for the translator bug:
 * When a relation is exactly bounded and used in override_with() + acyclic(),
 * the formula incorrectly reduces to constant FALSE (0 variables)
 */

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    // Create universe
    let u = Universe::new(&["a", "b", "c", "nil"]).unwrap();
    let mut bounds = Bounds::new(u);
    let t = bounds.universe().factory();

    // Create relations
    let r = Relation::binary("r");
    let nil = Relation::unary("nil");
    let a_rel = Relation::unary("a");

    // Bind nil exactly
    bounds.bound_exactly(&nil, t.tuple_set(&[&["nil"]]).unwrap()).unwrap();

    // Bind a to the atom "a"
    bounds.bound_exactly(&a_rel, t.tuple_set(&[&["a"]]).unwrap()).unwrap();

    // Bind r exactly to a specific value
    let mut r_tuples = t.none(2);
    r_tuples.add(t.tuple(&["a", "b"]).unwrap()).unwrap();
    r_tuples.add(t.tuple(&["b", "c"]).unwrap()).unwrap();
    r_tuples.add(t.tuple(&["c", "nil"]).unwrap()).unwrap();

    eprintln!("Test 1: with exact bounds on r");
    bounds.bound_exactly(&r, r_tuples.clone()).unwrap();

    // Create expression: r' = r.override(a -> nil)
    let a_expr = Expression::from(a_rel.clone());
    let nil_expr = Expression::from(nil.clone());
    let r_prime = Expression::from(r.clone()).override_with(a_expr.product(nil_expr));

    // Create formula: acyclic(r')
    let formula = r_prime.clone().closure().intersection(Expression::IDEN).no();

    eprintln!("Formula: acyclic(r.override(a -> nil))");

    let solver = Solver::new(Options::default());
    let result = solver.solve(&formula, &bounds).expect("Solve failed");

    eprintln!("Result: {:?}", result);
    eprintln!("Stats: {:?}\n", result.statistics());

    // Now try without exact bounds
    eprintln!("Test 2: with partial bounds on r");
    let u2 = Universe::new(&["a", "b", "c", "nil"]).unwrap();
    let mut bounds2 = Bounds::new(u2);
    let t2 = bounds2.universe().factory();

    bounds2.bound_exactly(&nil, t2.tuple_set(&[&["nil"]]).unwrap()).unwrap();
    bounds2.bound_exactly(&a_rel, t2.tuple_set(&[&["a"]]).unwrap()).unwrap();

    // Use partial bounds instead of exact
    let atoms_set = t2.tuple_set(&[&["a"], &["b"], &["c"], &["nil"]]).unwrap();
    let all_pairs = atoms_set.product(&atoms_set).unwrap();
    bounds2.bound(&r, r_tuples, all_pairs).unwrap();

    let result2 = solver.solve(&formula, &bounds2).expect("Solve failed");

    eprintln!("Result: {:?}", result2);
    eprintln!("Stats: {:?}", result2.statistics());
}
