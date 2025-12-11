//! Tests for unsat core extraction using assumptions

use kodkod_rs::engine::{rustsat_adapter::RustSatAdapter, SATSolver};
use rustsat_batsat::BasicSolver;

#[test]
fn test_unsat_core_simple() {
    // Test extracting unsat core using assumptions
    // Formula: (x1 OR x2) AND (NOT x1 OR x3) AND (NOT x2 OR x3) AND NOT x3
    // If we assume x1=true, x2=true, x3=false, we get UNSAT
    // Core should contain the conflicting assumptions

    let mut solver = RustSatAdapter::new(BasicSolver::default());
    solver.add_variables(3);

    // Add clauses (without unit clauses - we'll use assumptions instead)
    solver.add_clause(&[1, 2]);      // x1 OR x2
    solver.add_clause(&[-1, 3]);     // NOT x1 OR x3
    solver.add_clause(&[-2, 3]);     // NOT x2 OR x3

    // Try with assumptions that lead to UNSAT
    let assumptions = vec![1, 2, -3];  // x1=true, x2=true, x3=false

    let result = solver.solve_with_assumptions(&assumptions);
    assert!(!result, "Should be UNSAT with these assumptions");

    // Get the unsat core
    let core = solver.unsat_core();
    println!("Unsat core: {:?}", core);

    // Core should be non-empty and a subset of assumptions
    assert!(!core.is_empty(), "Core should not be empty");
    for lit in &core {
        assert!(assumptions.contains(lit), "Core literal {} should be in assumptions", lit);
    }
}

#[test]
fn test_unsat_core_minimal() {
    // Test that core is minimal for a simple contradiction
    let mut solver = RustSatAdapter::new(BasicSolver::default());
    solver.add_variables(2);

    // Add clauses: (x1) AND (NOT x1)  - directly contradictory
    solver.add_clause(&[1]);
    solver.add_clause(&[-1]);

    // Solve with no assumptions - should be UNSAT
    let result = solver.solve();
    assert!(!result, "Should be UNSAT");

    // Now test with assumptions
    let assumptions = vec![2];  // x2=true (irrelevant)
    let result = solver.solve_with_assumptions(&assumptions);
    assert!(!result, "Should still be UNSAT");

    let core = solver.unsat_core();
    println!("Core for irrelevant assumption: {:?}", core);
    // Core should be empty since x2 is not part of the conflict
    assert!(core.is_empty(), "Core should be empty for irrelevant assumptions");
}

#[test]
fn test_unsat_core_partial() {
    // Test extracting partial core when only some assumptions cause UNSAT
    let mut solver = RustSatAdapter::new(BasicSolver::default());
    solver.add_variables(3);

    // (x1 OR x2) AND (NOT x1 OR NOT x2)
    solver.add_clause(&[1, 2]);
    solver.add_clause(&[-1, -2]);

    // With assumptions x1=true, x2=true, x3=true
    // Only x1 and x2 cause the conflict
    let assumptions = vec![1, 2, 3];

    let result = solver.solve_with_assumptions(&assumptions);
    assert!(!result, "Should be UNSAT");

    let core = solver.unsat_core();
    println!("Partial core: {:?}", core);

    // Core should contain 1 and 2, but not necessarily 3
    assert!(core.contains(&1) || core.contains(&2),
            "Core should contain at least one of the conflicting literals");
}
