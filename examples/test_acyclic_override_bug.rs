/*
 * Precise test case for the translator bug in list_synth:
 * When a relation is exactly bounded and used in nested override_with() + acyclic(),
 * the formula incorrectly reduces to constant FALSE
 */

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn run() {
    // Create universe matching list_synth counterexample
    let u = Universe::new(&["l0", "n0", "n1", "n2", "nil"]).unwrap();
    let mut bounds = Bounds::new(u);
    let t = bounds.universe().factory();

    // Create relations like in list_synth
    let next = Relation::binary("next");
    let nil = Relation::unary("nil");

    // Bind nil exactly
    bounds.bound_exactly(&nil, t.tuple_set(&[&["nil"]]).unwrap()).unwrap();

    // Bind next exactly to match the counterexample pattern
    let mut next_tuples = t.none(2);
    next_tuples.add(t.tuple(&["n0", "n2"]).unwrap()).unwrap();
    next_tuples.add(t.tuple(&["n1", "n2"]).unwrap()).unwrap();
    next_tuples.add(t.tuple(&["n2", "nil"]).unwrap()).unwrap();

    eprintln!("Testing acyclic on override with exact bounds...");
    bounds.bound_exactly(&next, next_tuples.clone()).unwrap();

    // Create the pattern from list_synth:
    // next0 = next.override(n0 -> n2)  // simplified version
    // next1 = next0.override(n1 -> n0)
    // next2 = next0 (simplified - no conditional)
    // next3 = next2.override(n1 -> n0)

    let n0 = Relation::unary("n0");
    let n1 = Relation::unary("n1");
    let n2 = Relation::unary("n2");

    bounds.bound_exactly(&n0, t.tuple_set(&[&["n0"]]).unwrap()).unwrap();
    bounds.bound_exactly(&n1, t.tuple_set(&[&["n1"]]).unwrap()).unwrap();
    bounds.bound_exactly(&n2, t.tuple_set(&[&["n2"]]).unwrap()).unwrap();

    let next_expr = Expression::from(next.clone());
    let n0_expr = Expression::from(n0);
    let n1_expr = Expression::from(n1);
    let n2_expr = Expression::from(n2);

    // Mimic the list_synth pattern
    let next0 = next_expr.clone().override_with(n0_expr.clone().product(n2_expr.clone()));
    let next2 = next0.clone(); // simplified
    let next3 = next2.override_with(n1_expr.product(n0_expr.clone()));

    // The problematic formula: acyclic(next3)
    let formula = next3.clone().closure().intersection(Expression::IDEN).no();

    eprintln!("Formula: acyclic(next3) where next3 is built from override operations");

    let solver = Solver::new(Options::default());
    let result = solver.solve(&formula, &bounds).expect("Solve failed");

    eprintln!("Result: {:?}", match result {
        kodkod_rs::solver::Solution::Sat { .. } => "SAT",
        kodkod_rs::solver::Solution::Unsat { .. } => "UNSAT",
        kodkod_rs::solver::Solution::Trivial { is_true, .. } => {
            if is_true { "TRIVIALLY TRUE" } else { "TRIVIALLY FALSE" }
        }
    });
    eprintln!("Stats: {:?}", result.statistics());

    // Now test a simpler version to isolate the issue
    eprintln!("\nSimpler test: acyclic(next.override(n0 -> nil))");

    let nil_expr = Expression::from(nil);
    let next_simple = next_expr.override_with(n0_expr.product(nil_expr));
    let formula_simple = next_simple.clone().closure().intersection(Expression::IDEN).no();

    let result2 = solver.solve(&formula_simple, &bounds).expect("Solve failed");

    eprintln!("Result: {:?}", match result2 {
        kodkod_rs::solver::Solution::Sat { .. } => "SAT",
        kodkod_rs::solver::Solution::Unsat { .. } => "UNSAT",
        kodkod_rs::solver::Solution::Trivial { is_true, .. } => {
            if is_true { "TRIVIALLY TRUE" } else { "TRIVIALLY FALSE" }
        }
    });
    eprintln!("Stats: {:?}", result2.statistics());
}

fn main() {
    run()
}
#[test]
fn test_test_acyclic_override_bug_runs() {
    // Test that the example runs without panicking
    run();
}
