//! Test to demonstrate symmetry breaking impact on GroupScheduling

use kodkod_rs::{
    ast::*,
    instance::{Bounds, Universe},
    solver::{Options as SolverOptions, Solver},
};
use std::time::Instant;

fn test_group_scheduling(n: usize, with_symmetry_breaking: bool) {
    let num_groups = n;
    let num_persons = num_groups * num_groups;
    let num_rounds = num_groups + 1;

    // Build universe
    let mut atoms = Vec::new();
    for i in 0..num_persons {
        atoms.push(format!("p{}", i));
    }
    for i in 0..num_groups {
        atoms.push(format!("g{}", i));
    }
    for i in 0..num_rounds {
        atoms.push(format!("r{}", i));
    }

    let universe = Universe::new(&atoms.iter().map(|s| s.as_str()).collect::<Vec<_>>()).unwrap();
    let factory = universe.factory();

    // Relations
    let person = Relation::unary("Person");
    let group = Relation::unary("Group");
    let round = Relation::unary("Round");
    let assign = Relation::ternary("assign");

    // Bounds
    let mut bounds = Bounds::new(universe.clone());

    let person_range = factory.range(
        factory.tuple(&["p0"]).unwrap(),
        factory.tuple(&[&format!("p{}", num_persons - 1)]).unwrap()
    ).unwrap();
    bounds.bound_exactly(&person, person_range).unwrap();

    let group_range = factory.range(
        factory.tuple(&["g0"]).unwrap(),
        factory.tuple(&[&format!("g{}", num_groups - 1)]).unwrap()
    ).unwrap();
    bounds.bound_exactly(&group, group_range).unwrap();

    let round_range = factory.range(
        factory.tuple(&["r0"]).unwrap(),
        factory.tuple(&[&format!("r{}", num_rounds - 1)]).unwrap()
    ).unwrap();
    bounds.bound_exactly(&round, round_range).unwrap();

    let all_assign = factory.all(3);
    bounds.bound(&assign, factory.none(3), all_assign).unwrap();

    // Constraints (simplified - just C1 for this test)
    let p = Variable::unary("p");
    let r = Variable::unary("r");

    let c1_body = Expression::from(r.clone())
        .join(Expression::from(p.clone()).join(Expression::from(assign.clone())))
        .one();
    let c1 = Formula::forall(
        Decls::from(Decl::one_of(p.clone(), Expression::from(person.clone())))
            .and(Decl::one_of(r.clone(), Expression::from(round.clone()))),
        c1_body,
    );

    // Configure solver
    let mut opts = SolverOptions::default();
    opts.symmetry_breaking = if with_symmetry_breaking { 20 } else { 0 };
    let solver = Solver::new(opts);

    // Solve
    let start = Instant::now();
    let solution = solver.solve(&c1, &bounds).expect("Solver failed");
    let elapsed = start.elapsed();

    println!("N={}, Symmetry Breaking: {}", n, if with_symmetry_breaking { "ON " } else { "OFF" });
    println!("  Result: {}", if solution.is_sat() { "SAT  " } else { "UNSAT" });
    println!("  Time: {:.0}ms", elapsed.as_secs_f64() * 1000.0);
    println!("  Variables: {}, Clauses: {}",
        solution.statistics().num_variables(),
        solution.statistics().num_clauses());
}

fn main() {
    println!("\n=== SYMMETRY BREAKING IMPACT TEST ===\n");

    for n in [2, 3] {
        test_group_scheduling(n, false);
        test_group_scheduling(n, true);
        println!();
    }
}
