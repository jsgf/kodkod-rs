//! Trivial solver test - just boolean formulas

use kodkod_rs::ast::Formula;
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    println!("=== Trivial Test: Boolean Formulas ===\n");

    // Test 1: TRUE should be SAT
    {
        println!("Test 1: Formula::TRUE");
        let universe = Universe::new(&["A"]).unwrap();
        let bounds = Bounds::new(universe);
        let solver = Solver::new(Options::default());

        match solver.solve(&Formula::TRUE, &bounds) {
            Ok(solution) => {
                if solution.is_sat() {
                    println!("  ✓ SAT (correct!)");
                    println!("    Variables: {}", solution.statistics().num_variables());
                    println!("    Clauses: {}", solution.statistics().num_clauses());
                } else {
                    println!("  ✗ UNSAT (WRONG!)");
                }
            }
            Err(e) => println!("  ERROR: {}", e),
        }
    }

    println!();

    // Test 2: FALSE should be UNSAT
    {
        println!("Test 2: Formula::FALSE");
        let universe = Universe::new(&["A"]).unwrap();
        let bounds = Bounds::new(universe);
        let solver = Solver::new(Options::default());

        match solver.solve(&Formula::FALSE, &bounds) {
            Ok(solution) => {
                if solution.is_unsat() {
                    println!("  ✓ UNSAT (correct!)");
                } else {
                    println!("  ✗ SAT (WRONG!)");
                }
            }
            Err(e) => println!("  ERROR: {}", e),
        }
    }

    println!();

    // Test 3: TRUE AND FALSE should be UNSAT
    {
        println!("Test 3: TRUE AND FALSE");
        let universe = Universe::new(&["A"]).unwrap();
        let bounds = Bounds::new(universe);
        let solver = Solver::new(Options::default());

        let formula = Formula::and(Formula::TRUE, Formula::FALSE);

        match solver.solve(&formula, &bounds) {
            Ok(solution) => {
                if solution.is_unsat() {
                    println!("  ✓ UNSAT (correct!)");
                } else {
                    println!("  ✗ SAT (WRONG!)");
                }
            }
            Err(e) => println!("  ERROR: {}", e),
        }
    }

    println!();

    // Test 4: TRUE OR FALSE should be SAT
    {
        println!("Test 4: TRUE OR FALSE");
        let universe = Universe::new(&["A"]).unwrap();
        let bounds = Bounds::new(universe);
        let solver = Solver::new(Options::default());

        let formula = Formula::or(Formula::TRUE, Formula::FALSE);

        match solver.solve(&formula, &bounds) {
            Ok(solution) => {
                if solution.is_sat() {
                    println!("  ✓ SAT (correct!)");
                } else {
                    println!("  ✗ UNSAT (WRONG!)");
                }
            }
            Err(e) => println!("  ERROR: {}", e),
        }
    }
}
