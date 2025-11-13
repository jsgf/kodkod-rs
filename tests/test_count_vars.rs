//! Test cardinality with variables

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    println!("=== Cardinality with variables ===\n");

    let people = Relation::unary("People");
    let likes = Relation::binary("Likes");

    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let factory = universe.factory();

    let mut bounds = Bounds::new(universe);

    // People = {A, B, C}
    let people_tuples = vec![vec!["A"], vec!["B"], vec!["C"]];
    let people_refs: Vec<&[&str]> = people_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&people, factory.tuple_set(&people_refs).unwrap()).unwrap();

    // Likes: lower=empty, upper=all pairs
    let all_binary = factory.all(2);
    bounds.bound(&likes, factory.none(2), all_binary).unwrap();

    let solver = Solver::new(Options::default());

    // Test: exists p: People | p.likes.count() > 0
    println!("Test: exists p: People | p.likes.count() > 0");
    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_likes = p_expr.join(Expression::from(likes.clone()));
    let p_count = p_likes.count();
    let formula = Formula::exists(
        Decls::from(Decl::one_of(&p, &Expression::from(people.clone()))),
        p_count.gt(kodkod_rs::ast::IntExpression::constant(0))
    );

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}\n", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}\n", e),
    }

    // Test: all p: People | p.likes.count() >= 0 (trivially true)
    println!("Test: all p: People | p.likes.count() >= 0");
    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_likes = p_expr.join(Expression::from(likes.clone()));
    let p_count = p_likes.count();
    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(people.clone()))),
        p_count.gte(kodkod_rs::ast::IntExpression::constant(0))
    );

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}\n", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}\n", e),
    }

    // Test: all p, q: People | p.likes.count() != q.likes.count()
    println!("Test: all p, q: People | p.likes.count() != q.likes.count()");
    let p = Variable::unary("p");
    let q = Variable::unary("q");
    let p_expr = Expression::from(p.clone());
    let q_expr = Expression::from(q.clone());
    let p_count = p_expr.join(Expression::from(likes.clone())).count();
    let q_count = q_expr.join(Expression::from(likes.clone())).count();
    let different = p_count.eq(q_count).not();
    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(people.clone())))
            .and(Decl::one_of(&q, &Expression::from(people.clone()))),
        different
    );

    match solver.solve(&formula, &bounds) {
        Ok(sol) => {
            println!("Result: {}", if sol.is_sat() { "SAT" } else { "UNSAT" });
            println!("Vars: {}, Clauses: {}", sol.statistics().num_variables(), sol.statistics().num_clauses());
        },
        Err(e) => println!("Error: {:?}", e),
    }
}
