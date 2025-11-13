//! Minimal tests for translation and quantifiers

use kodkod_rs::ast::*;
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Solver, Options};

#[test]
fn test_some_relation() {
    // Create universe {1, 2}
    let universe = Universe::new(&["1", "2"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());
    let factory = bounds.universe().factory();

    // Create a binary relation R with no lower bound, full upper bound
    let r = Relation::binary("R");
    let lower = factory.none(2);
    let upper = factory.all(2);

    bounds.bound(&r, lower, upper).unwrap();

    // Test: some R (should be SAT with variables)
    let formula = Expression::from(r.clone()).some();

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds).unwrap();

    assert!(solution.is_sat(), "some R should be SAT");
    assert!(solution.statistics().num_variables() > 0, "Should have variables");
}

#[test]
fn test_forall_quantifier() {
    // Create universe {1, 2}
    let universe = Universe::new(&["1", "2"]).unwrap();
    let mut bounds = Bounds::new(universe.clone());
    let factory = bounds.universe().factory();

    // Create a binary relation R
    let r = Relation::binary("R");
    bounds.bound(&r, factory.none(2), factory.all(2)).unwrap();

    // Universe relation
    let univ_rel = Relation::unary("U");
    bounds.bound_exactly(&univ_rel, factory.all(1)).unwrap();

    // forall x,y: U | (x, y) in R
    let x = Variable::unary("x");
    let y = Variable::unary("y");
    let decls = Decls::from(Decl::one_of(x.clone(), Expression::from(univ_rel.clone())))
        .and(Decl::one_of(y.clone(), Expression::from(univ_rel.clone())));

    // (x, y) in R
    let xy = Expression::from(x.clone()).product(Expression::from(y.clone()));
    let body = xy.in_set(Expression::from(r.clone()));

    let formula = Formula::forall(decls, body);

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds).unwrap();

    assert!(solution.is_sat(), "forall x,y | (x,y) in R should be SAT");

    // Check that R contains all 4 tuples in the solution
    if let Some(inst) = solution.instance() {
        if let Some(r_tuples) = inst.get(&r) {
            assert_eq!(r_tuples.size(), 4, "R should contain all 4 tuples");
        }
    }
}
