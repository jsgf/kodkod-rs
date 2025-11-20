//! Netconfig example - network configuration problem
//!
//! A computational problem that should take a few seconds to solve.

use kodkod_rs::{
    ast::*,
    instance::{Bounds, Universe},
    solver::{Options as SolverOptions, Solver},
};
use std::time::Instant;

fn main() {
    let scope = std::env::args()
        .nth(1)
        .and_then(|arg| arg.parse::<usize>().ok())
        .unwrap_or(5);

    println!("=== Network Configuration Problem (scope: {}) ===\n", scope);

    let start = Instant::now();
    let solver = Solver::new(SolverOptions::default());

    // Relations
    let host = Relation::unary("Host");
    let link = Relation::binary("link");
    let active = Relation::unary("active");

    // Build universe with N hosts
    let mut atoms = Vec::new();
    for i in 0..scope {
        atoms.push(format!("h{}", i));
    }

    let universe = Universe::new(&atoms.iter().map(|s| s.as_str()).collect::<Vec<_>>())
        .expect("Failed to create universe");
    let factory = universe.factory();

    // Build bounds
    let mut bounds = Bounds::new(universe.clone());

    // All hosts
    let all_hosts = factory.all(1);
    bounds.bound_exactly(&host, all_hosts).expect("Failed to bind host");

    // Links: any pair of distinct hosts can be linked
    let all_pairs = factory.all(2);
    bounds.bound(&link, factory.none(2), all_pairs).expect("Failed to bind link");

    // Active hosts: subset of hosts
    let all_active = factory.all(1);
    bounds.bound(&active, factory.none(1), all_active).expect("Failed to bind active");

    let build_time = start.elapsed();

    // Build constraints
    let constraint_start = Instant::now();

    let h1 = Variable::unary("h1");
    let h2 = Variable::unary("h2");

    // Constraint 1: Links are symmetric (if h1-h2 then h2-h1)
    let c1_body = Expression::from(h1.clone())
        .product(Expression::from(h2.clone()))
        .in_relation(&link)
        .implies(
            Expression::from(h2.clone())
                .product(Expression::from(h1.clone()))
                .in_relation(&link),
        );
    let c1 = Formula::forall(
        Decls::from(Decl::one_of(h1.clone(), Expression::from(host.clone())))
            .and(Decl::one_of(h2.clone(), Expression::from(host.clone()))),
        c1_body,
    );

    // Constraint 2: No self-loops
    let c2_body = Expression::from(h1.clone())
        .product(Expression::from(h1.clone()))
        .in_relation(&link)
        .not();
    let c2 = Formula::forall(
        Decls::from(Decl::one_of(h1.clone(), Expression::from(host.clone()))),
        c2_body,
    );

    // Constraint 3: At least one host must be active
    let c3 = Expression::from(active.clone()).some();

    // Constraint 4: All active hosts must be connected via links
    let c4_inner_body = Expression::from(h2.clone())
        .in_relation(&active)
        .and(
            Expression::from(h1.clone())
                .ne(Expression::from(h2.clone()))
                .and(
                    Expression::from(h1.clone())
                        .product(Expression::from(h2.clone()))
                        .in_relation(&link),
                ),
        );
    let c4_inner = Formula::exists(
        Decls::from(Decl::one_of(h2.clone(), Expression::from(host.clone()))),
        c4_inner_body,
    );
    let c4_body = Expression::from(h1.clone())
        .in_relation(&active)
        .implies(c4_inner);
    let c4 = Formula::forall(
        Decls::from(Decl::one_of(h1.clone(), Expression::from(host.clone()))),
        c4_body,
    );

    let formula = Formula::and(c1, Formula::and(c2, Formula::and(c3, c4)));

    let constraint_time = constraint_start.elapsed();

    // Solve
    let solve_start = Instant::now();
    let solution = solver.solve(&formula, &bounds).expect("Solver failed");
    let _solve_time = solve_start.elapsed();

    println!(
        "Result: {}\n",
        if solution.is_sat() { "SAT" } else { "UNSAT" }
    );

    if let Some(_instance) = solution.instance() {
        println!("Solution found!");
    }

    let stats = solution.statistics();
    println!(
        "\nSolving Statistics:\n\
         Variables: {}\n\
         Clauses: {}\n\
         Build time: {:.2}ms\n\
         Constraint time: {:.2}ms\n\
         Translation time: {}ms\n\
         Solving time: {}ms\n\
         Total time: {:.2}s",
        stats.num_variables(),
        stats.num_clauses(),
        build_time.as_secs_f64() * 1000.0,
        constraint_time.as_secs_f64() * 1000.0,
        stats.translation_time(),
        stats.solving_time(),
        (build_time.as_secs_f64()
            + constraint_time.as_secs_f64()
            + stats.total_time() as f64 / 1000.0)
    );
}
