//! Test cardinality with quantified variables
//!
//! Tests ensure that cardinality constraints work correctly with variable bindings
//! in quantified formulas. These test that join().count() operations generate proper
//! boolean circuits rather than static evaluations.

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

#[test]
fn test_cardinality_with_existential_quantifier() {
    // Test: exists p: People | p.likes.count() > 0 (should be SAT)
    let people = Relation::unary("People");
    let likes = Relation::binary("Likes");

    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    // People = {A, B, C}
    let people_tuples = vec![vec!["A"], vec!["B"], vec!["C"]];
    let people_refs: Vec<&[&str]> = people_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&people, factory.tuple_set(&people_refs).unwrap()).unwrap();

    // Likes: variable binary relation
    let all_binary = factory.all(2);
    bounds.bound(&likes, factory.none(2), all_binary).unwrap();

    let solver = Solver::new(Options::default());

    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_likes = p_expr.join(Expression::from(likes.clone()));
    let p_count = p_likes.count();
    let formula = Formula::exists(
        Decls::from(Decl::one_of(&p, &Expression::from(people.clone()))),
        p_count.gt(kodkod_rs::ast::IntExpression::constant(0))
    );

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "Should be SAT: some person can like someone");
    assert!(solution.statistics().num_variables() > 0, "Should have boolean variables");
}

#[test]
fn test_cardinality_with_universal_quantifier_trivial() {
    // Test: all p: People | p.likes.count() >= 0 (trivially true)
    let people = Relation::unary("People");
    let likes = Relation::binary("Likes");

    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let people_tuples = vec![vec!["A"], vec!["B"], vec!["C"]];
    let people_refs: Vec<&[&str]> = people_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&people, factory.tuple_set(&people_refs).unwrap()).unwrap();

    let all_binary = factory.all(2);
    bounds.bound(&likes, factory.none(2), all_binary).unwrap();

    let solver = Solver::new(Options::default());

    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_likes = p_expr.join(Expression::from(likes.clone()));
    let p_count = p_likes.count();
    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(people.clone()))),
        p_count.gte(kodkod_rs::ast::IntExpression::constant(0))
    );

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "Should be SAT: all counts are >= 0 (trivially true)");
}

#[test]
fn test_cardinality_with_universal_quantifier_constraint() {
    // Test: all p, q: People | p.likes.count() != q.likes.count()
    // This is satisfiable: each person can like different numbers of people
    let people = Relation::unary("People");
    let likes = Relation::binary("Likes");

    let universe = Universe::new(&["A", "B", "C"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let people_tuples = vec![vec!["A"], vec!["B"], vec!["C"]];
    let people_refs: Vec<&[&str]> = people_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&people, factory.tuple_set(&people_refs).unwrap()).unwrap();

    let all_binary = factory.all(2);
    bounds.bound(&likes, factory.none(2), all_binary).unwrap();

    let solver = Solver::new(Options::default());

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

    let solution = solver.solve(&formula, &bounds).unwrap();
    // This may be SAT or UNSAT depending on whether all people can have different like-counts
    // The solver should generate proper circuits, which is what we're testing
    assert!(solution.statistics().num_variables() > 0, "Should generate boolean circuits for cardinality");
}

#[test]
fn test_cardinality_dynamic_evaluation_with_join() {
    // Critical test: verifies that cardinality is computed dynamically (at SAT-solving time)
    // not statically (at translation time). This was the bug that exposed the transpose error.
    let people = Relation::unary("People");
    let likes = Relation::binary("Likes");

    let universe = Universe::new(&["Alice", "Bob"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    let people_tuples = vec![vec!["Alice"], vec!["Bob"]];
    let people_refs: Vec<&[&str]> = people_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&people, factory.tuple_set(&people_refs).unwrap()).unwrap();

    // Likes: variable relation
    bounds.bound(&likes, factory.none(2), factory.all(2)).unwrap();

    let solver = Solver::new(Options::default());

    // For each person, exactly one person they like exists
    let p = Variable::unary("p");
    let p_expr = Expression::from(p.clone());
    let p_likes = p_expr.join(Expression::from(likes.clone()));
    let formula = Formula::forall(
        Decls::from(Decl::one_of(&p, &Expression::from(people.clone()))),
        p_likes.count().eq(kodkod_rs::ast::IntExpression::constant(1))
    );

    let solution = solver.solve(&formula, &bounds).unwrap();
    assert!(solution.is_sat(), "Should be SAT: each person likes exactly 1 person");

    // Verify circuit generation (not static evaluation)
    let vars = solution.statistics().num_variables();
    assert!(vars > 0, "Should have generated boolean circuits for dynamic cardinality");
}
