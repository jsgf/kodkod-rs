//! Minimal test to debug Handshake count expressions

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    println!("=== Testing count() with forall ===\n");

    // Create relations
    let person = Relation::unary("Person");
    let shaken = Relation::binary("shaken");

    // Create universe with 3 people
    let universe = Universe::new(&["P1", "P2", "P3"]).unwrap();
    let factory = universe.factory();

    let mut bounds = Bounds::new(universe);

    // Person: all atoms
    let person_tuples = vec![vec!["P1"], vec!["P2"], vec!["P3"]];
    let person_refs: Vec<&[&str]> = person_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&person, factory.tuple_set(&person_refs).unwrap()).unwrap();

    // shaken: all binary tuples (everyone can shake hands with everyone)
    let all_binary = factory.all(2);
    bounds.bound(&shaken, factory.none(2), all_binary).unwrap();

    // Test 1: Simple - just count handshakes for a person
    println!("Test 1: Simple count");
    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_shaken = p_expr.join(Expression::from(shaken.clone()));
    let p_count = p_shaken.count();
    println!("Formula: p.shaken.count() > 0");
    let formula = p_count.gt(kodkod_rs::ast::IntExpression::constant(0));

    let solver = Solver::new(Options::default());
    match solver.solve(&formula, &bounds) {
        Ok(sol) => println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" }),
        Err(e) => println!("Error: {:?}", e),
    }

    // Test 2: Count with forall (no disj)
    println!("\nTest 2: Count with forall (no disjoint)");
    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_count = p_expr.join(Expression::from(shaken.clone())).count();
    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(person.clone()))),
        p_count.gt(kodkod_rs::ast::IntExpression::constant(-1))
    );
    println!("Formula: all p: Person | p.shaken.count() > -1");

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}", e),
    }

    // Test 3: Count comparison with forall and two variables
    println!("\nTest 3: Count comparison with forall (two vars, no disj)");
    let p = Variable::unary("p");
    let q = Variable::unary("q");

    let p_expr = Expression::from(p.clone());
    let q_expr = Expression::from(q.clone());

    let p_count = p_expr.join(Expression::from(shaken.clone())).count();
    let q_count = q_expr.join(Expression::from(shaken.clone())).count();

    let different = p_count.eq(q_count).not();

    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(person.clone())))
            .and(Decl::one_of(&q, &Expression::from(person.clone()))),
        different
    );
    println!("Formula: all p, q: Person | p.shaken.count() != q.shaken.count()");

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}", e),
    }

    // Test 4: Same but with intersection (disjoint-like)
    println!("\nTest 4: Count with disjoint constraint");
    let p = Variable::unary("p");
    let q = Variable::unary("q");

    let p_expr = Expression::from(p.clone());
    let q_expr = Expression::from(q.clone());

    let disjoint = p_expr.clone().intersection(q_expr.clone()).no();
    let p_count = p_expr.join(Expression::from(shaken.clone())).count();
    let q_count = q_expr.join(Expression::from(shaken.clone())).count();
    let different = p_count.eq(q_count).not();

    let body = disjoint.implies(different);

    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(person.clone())))
            .and(Decl::one_of(&q, &Expression::from(person.clone()))),
        body
    );
    println!("Formula: all p, q: Person | (p ∩ q).no() => p.shaken.count() != q.shaken.count()");

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}", e),
    }
}
