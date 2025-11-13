//! Simple cardinality test

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    println!("=== Simple cardinality test ===\n");

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
    println!("Test: items.count() == 2");
    let items_expr = Expression::from(items.clone());
    let items_count = items_expr.count();
    let formula = items_count.eq(kodkod_rs::ast::IntExpression::constant(2));

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}", e),
    }

    // Test: Items.count() == 3 (should be UNSAT)
    println!("\nTest: items.count() == 3 (should be UNSAT)");
    let items_expr = Expression::from(items.clone());
    let items_count = items_expr.count();
    let formula = items_count.eq(kodkod_rs::ast::IntExpression::constant(3));

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}", e),
    }
}
