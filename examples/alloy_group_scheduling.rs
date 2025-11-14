//! Group Scheduling problem
//!
//! Constraint satisfaction problem where N^2 people must be scheduled into N groups
//! across N+1 rounds such that:
//! 1. Each person is in exactly one group per round
//! 2. Each group has exactly N people per round
//! 3. No two people meet more than once across all rounds
//!
//! Based on: kodkod.examples.alloy.GroupScheduling

use kodkod_rs::{
    ast::*,
    instance::{Bounds, Universe},
    solver::{Options as SolverOptions, Solver},
};
use std::time::Instant;

fn main() {
    let num_groups = std::env::args()
        .nth(1)
        .and_then(|arg| arg.parse::<usize>().ok())
        .unwrap_or(3);

    println!(
        "=== Group Scheduling Problem (groups: {}, persons: {}) ===\n",
        num_groups,
        num_groups * num_groups
    );

    let start = Instant::now();
    let solver = Solver::new(SolverOptions::default());

    // Relations
    let person = Relation::unary("Person");
    let group = Relation::unary("Group");
    let round = Relation::unary("Round");
    let assign = Relation::ternary("assign"); // (Person, Round, Group)

    // Universe: N^2 persons, N groups, N+1 rounds
    let num_persons = num_groups * num_groups;
    let num_rounds = num_groups + 1;

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

    let universe = Universe::new(&atoms.iter().map(|s| s.as_str()).collect::<Vec<_>>())
        .expect("Failed to create universe");
    let factory = universe.factory();

    // Build bounds
    let mut bounds = Bounds::new(universe.clone());

    // Bind person to p0..p(num_persons-1)
    let person_range = factory
        .range(
            factory.tuple(&["p0"]).unwrap(),
            factory
                .tuple(&[&format!("p{}", num_persons - 1)])
                .unwrap(),
        )
        .unwrap();
    bounds.bound_exactly(&person, person_range);

    // Bind group to g0..g(num_groups-1)
    let group_range = factory
        .range(
            factory.tuple(&["g0"]).unwrap(),
            factory
                .tuple(&[&format!("g{}", num_groups - 1)])
                .unwrap(),
        )
        .unwrap();
    bounds.bound_exactly(&group, group_range.clone());

    // Bind round to r0..r(num_rounds-1)
    let round_range = factory
        .range(
            factory.tuple(&["r0"]).unwrap(),
            factory
                .tuple(&[&format!("r{}", num_rounds - 1)])
                .unwrap(),
        )
        .unwrap();
    bounds.bound_exactly(&round, round_range.clone());

    // Assignments with symmetry breaking bounds
    // Lower bound: force specific people into group 0 for each round
    let mut lower_assign = factory.none(3);
    for i in 0..num_rounds {
        // p0 is in g0 for every round
        lower_assign
            .add(factory.tuple(&["p0", &format!("r{}", i), "g0"]).unwrap())
            .unwrap();

        // For each round i, persons p[i*(ng-1)+1] through p[(i+1)*(ng-1)] are in g0
        let start = i * (num_groups - 1) + 1;
        let end = (i + 1) * (num_groups - 1);
        if start <= end && end < num_persons {
            let person_range = factory
                .range(
                    factory.tuple(&[&format!("p{}", start)]).unwrap(),
                    factory.tuple(&[&format!("p{}", end)]).unwrap(),
                )
                .unwrap();
            let round_set = factory.set_of(&format!("r{}", i)).unwrap();
            let group_set = factory.set_of("g0").unwrap();

            let product = person_range
                .product(&round_set)
                .unwrap()
                .product(&group_set)
                .unwrap();
            lower_assign.add_all(&product).unwrap();
        }
    }

    // Upper bound: lower bound + all assignments for p1..p(num_persons-1)
    let mut upper_assign = factory.none(3);
    upper_assign.add_all(&lower_assign).unwrap();

    if num_persons > 1 {
        let persons_1_to_end = factory
            .range(
                factory.tuple(&["p1"]).unwrap(),
                factory
                    .tuple(&[&format!("p{}", num_persons - 1)])
                    .unwrap(),
            )
            .unwrap();
        let all_assignments = persons_1_to_end
            .product(&round_range)
            .unwrap()
            .product(&group_range)
            .unwrap();
        upper_assign.add_all(&all_assignments).unwrap();
    }

    bounds.bound(&assign, lower_assign, upper_assign);

    let build_time = start.elapsed();

    // Build constraints
    let constraint_start = Instant::now();

    let p = Variable::unary("p");
    let pp = Variable::unary("p'");
    let r = Variable::unary("r");
    let g = Variable::unary("g");

    // C1: Each person is in exactly one group per round
    // forall p, r | one (r.(p.assign))
    let c1_body = Expression::from(r.clone())
        .join(Expression::from(p.clone()).join(Expression::from(assign.clone())))
        .one();
    let c1 = Formula::forall(
        Decls::from(Decl::one_of(p.clone(), Expression::from(person.clone())))
            .and(Decl::one_of(r.clone(), Expression::from(round.clone()))),
        c1_body,
    );

    // C2: Each group has exactly N people per round
    // forall r, g | #(assign.g.r) = N
    let c2_body = Expression::from(assign.clone())
        .join(Expression::from(g.clone()))
        .join(Expression::from(r.clone()))
        .count()
        .eq(IntExpression::constant(num_groups as i32));
    let c2 = Formula::forall(
        Decls::from(Decl::one_of(r.clone(), Expression::from(round.clone())))
            .and(Decl::one_of(g.clone(), Expression::from(group.clone()))),
        c2_body,
    );

    // C3: Every pair of people meets at least once
    // forall p, p' != p | some (p.assign intersect p'.assign)
    let c3_inner = Expression::from(p.clone())
        .join(Expression::from(assign.clone()))
        .intersection(
            Expression::from(pp.clone()).join(Expression::from(assign.clone())),
        )
        .some();
    let c3_body = Formula::forall(
        Decls::from(Decl::one_of(pp.clone(), Expression::from(person.clone()).difference(Expression::from(p.clone())))),
        c3_inner,
    );
    let c3 = Formula::forall(
        Decls::from(Decl::one_of(p.clone(), Expression::from(person.clone()))),
        c3_body,
    );

    let formula = Formula::and(c1, Formula::and(c2, c3));

    let constraint_time = constraint_start.elapsed();

    // Solve
    let solve_start = Instant::now();
    let solution = solver.solve(&formula, &bounds).expect("Solver failed");
    let solve_time = solve_start.elapsed();

    println!(
        "Result: {}\n",
        if solution.is_sat() { "SAT" } else { "UNSAT" }
    );

    if let Some(_instance) = solution.instance() {
        println!("Valid schedule found!");
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
