//! Test for empty set handling bug

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Testing empty set handling ===\n");

    // Simple universe with 3 atoms
    let atoms = vec!["0", "1", "2"];
    let universe = Universe::new(&atoms)?;
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    // Create a linear ordering: 0 -> 1 -> 2
    let ord = Relation::binary("ord");
    let ord_tuples = vec![vec!["0", "1"], vec!["1", "2"]];
    let ord_refs: Vec<Vec<&str>> = ord_tuples.iter()
        .map(|v| v.iter().map(|s| *s).collect())
        .collect();
    let ord_tuple_refs: Vec<&[&str]> = ord_refs.iter().map(|v| v.as_slice()).collect();
    let ord_bound = factory.tuple_set(&ord_tuple_refs)?;
    bounds.bound_exactly(&ord, ord_bound)?;

    // Test 1: prev(first) should be empty
    println!("Test 1: prev(0) with ord = {{(0,1), (1,2)}}");
    let atom0 = Relation::unary("atom0");
    bounds.bound_exactly(&atom0, factory.set_of("0")?)?;

    let formula1 = Expression::from(ord.clone())
        .join(Expression::from(atom0.clone()))
        .no();  // prev(0) should be empty

    let solver = Solver::new(Options::default());
    let solution1 = solver.solve(&formula1, &bounds)?;

    println!("  prev(0).no() = {}", if solution1.is_sat() { "TRUE" } else { "FALSE" });
    println!("  Variables: {}, Clauses: {}",
        solution1.statistics().num_variables(),
        solution1.statistics().num_clauses());

    // Test 2: Using prev in a product
    println!("\nTest 2: prev(x).product(y) where x can be any atom");
    let cell = Relation::unary("Cell");
    let cell_bound = factory.all(1);
    bounds.bound_exactly(&cell, cell_bound)?;

    let x = Variable::unary("x");
    let y = Variable::unary("y");

    let prev_x = Expression::from(ord.clone()).join(Expression::from(x.clone()));
    let neighbors = prev_x.product(Expression::from(y.clone()));

    // For x=0, prev(x) is empty, so neighbors should be empty
    // For x=1, prev(x)={0}, so neighbors={(0,y) for all y}
    // For x=2, prev(x)={1}, so neighbors={(1,y) for all y}

    let formula2 = Formula::forall(
        Decls::from(Decl::one_of(x, Expression::from(cell.clone())))
            .and(Decl::one_of(y, Expression::from(cell.clone()))),
        neighbors.clone().no().or(neighbors.some())  // Should always be true
    );

    let solution2 = solver.solve(&formula2, &bounds)?;
    println!("  Result: {}", if solution2.is_sat() { "SAT" } else { "UNSAT" });
    println!("  Variables: {}, Clauses: {}",
        solution2.statistics().num_variables(),
        solution2.statistics().num_clauses());

    Ok(())
}
