//! Translator tests for comparison formulas
//!
//! Following Java: kodkod.test.unit.TranslatorTest.testTranslateComparisonFormula
//! Tests that comparison formulas (equals, subset/in) translate correctly

use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn create_test_bounds() -> (Bounds, Vec<Relation>, Vec<Relation>, Vec<Relation>) {
    let universe = Universe::new(&["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]).unwrap();
    let factory = universe.factory();

    let mut r1 = Vec::new();
    let mut r2 = Vec::new();
    let mut r3 = Vec::new();

    for i in 0..4 {
        r1.push(Relation::unary(&format!("r1{i}")));
        r2.push(Relation::binary(&format!("r2{i}")));
        r3.push(Relation::ternary(&format!("r3{i}")));
    }

    let mut bounds = Bounds::new(universe);

    // r1[0]: all of arity 1
    bounds.bound(&r1[0], factory.none(1), factory.all(1)).unwrap();

    // r1[1]: range from 2 to 4
    let lower = factory.none(1);
    let upper = factory.range(
        factory.tuple(&["2"]).unwrap(),
        factory.tuple(&["4"]).unwrap()
    ).unwrap();
    bounds.bound(&r1[1], lower, upper).unwrap();

    // r1[2]: exactly {4}
    let exact = factory.tuple_set(&[&["4"]]).unwrap();
    bounds.bound_exactly(&r1[2], exact).unwrap();

    // r1[3]: range from 5 to 8
    let lower = factory.none(1);
    let upper = factory.range(
        factory.tuple(&["5"]).unwrap(),
        factory.tuple(&["8"]).unwrap()
    ).unwrap();
    bounds.bound(&r1[3], lower, upper).unwrap();

    // r2[0]: all of arity 2
    bounds.bound(&r2[0], factory.none(2), factory.all(2)).unwrap();

    // r2[1]: area from (2,3) to (2,5)
    let lower = factory.none(2);
    let upper = factory.area(
        factory.tuple(&["2", "3"]).unwrap(),
        factory.tuple(&["2", "5"]).unwrap()
    ).unwrap();
    bounds.bound(&r2[1], lower, upper).unwrap();

    // r2[2]: exactly {(2,5)}
    let exact = factory.tuple_set(&[&["2", "5"]]).unwrap();
    bounds.bound_exactly(&r2[2], exact).unwrap();

    // r2[3]: area from (2,6) to (2,8)
    let lower = factory.none(2);
    let upper = factory.area(
        factory.tuple(&["2", "6"]).unwrap(),
        factory.tuple(&["2", "8"]).unwrap()
    ).unwrap();
    bounds.bound(&r2[3], lower, upper).unwrap();

    // r3[0]: all of arity 3
    bounds.bound(&r3[0], factory.none(3), factory.all(3)).unwrap();

    // r3[1]: area from (3,1,2) to (3,3,4)
    let lower = factory.none(3);
    let upper = factory.area(
        factory.tuple(&["3", "1", "2"]).unwrap(),
        factory.tuple(&["3", "3", "4"]).unwrap()
    ).unwrap();
    bounds.bound(&r3[1], lower, upper).unwrap();

    // r3[2]: exactly {(3,3,4)}
    let exact = factory.tuple_set(&[&["3", "3", "4"]]).unwrap();
    bounds.bound_exactly(&r3[2], exact).unwrap();

    // r3[3]: area from (3,7,0) to (3,8,9)
    let lower = factory.none(3);
    let upper = factory.area(
        factory.tuple(&["3", "7", "0"]).unwrap(),
        factory.tuple(&["3", "8", "9"]).unwrap()
    ).unwrap();
    bounds.bound(&r3[3], lower, upper).unwrap();

    (bounds, r1, r2, r3)
}

#[test]
fn test_reflexive_subset() {
    // Following Java: for all relations, r in r (reflexive subset)
    let (bounds, r1, r2, r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    for i in 0..4 {
        // r1[i] in r1[i]
        let formula = Expression::from(r1[i].clone()).in_set(Expression::from(r1[i].clone()));
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r1[{i}] in r1[{i}] should be SAT");

        // r2[i] in r2[i]
        let formula = Expression::from(r2[i].clone()).in_set(Expression::from(r2[i].clone()));
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r2[{i}] in r2[{i}] should be SAT");

        // r3[i] in r3[i]
        let formula = Expression::from(r3[i].clone()).in_set(Expression::from(r3[i].clone()));
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r3[{i}] in r3[{i}] should be SAT");
    }
}

#[test]
fn test_subset_with_intersection() {
    // Following Java: some rx2 && (rx1 & rx2 in rx2)
    // Tests that intersection is subset of one of the operands
    let (bounds, r1, r2, r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // some r1[2] && (r1[1] & r1[2] in r1[2])
    let formula = Expression::from(r1[2].clone()).some()
        .and(Expression::from(r1[1].clone()).intersection(Expression::from(r1[2].clone()))
             .in_set(Expression::from(r1[2].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r1[1] & r1[2] should be subset of r1[2]");

    // some r2[2] && (r2[1] & r2[2] in r2[2])
    let formula = Expression::from(r2[2].clone()).some()
        .and(Expression::from(r2[1].clone()).intersection(Expression::from(r2[2].clone()))
             .in_set(Expression::from(r2[2].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r2[1] & r2[2] should be subset of r2[2]");

    // some r3[2] && (r3[1] & r3[2] in r3[2])
    let formula = Expression::from(r3[2].clone()).some()
        .and(Expression::from(r3[1].clone()).intersection(Expression::from(r3[2].clone()))
             .in_set(Expression::from(r3[2].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r3[1] & r3[2] should be subset of r3[2]");
}

#[test]
fn test_equals_with_intersection() {
    // Following Java: one rx2 && (rx1 & rx2 = rx2)
    // Tests equality when rx2 is singleton and subset of rx1
    let (bounds, r1, r2, r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // one r1[2] && (r1[1] & r1[2] = r1[2])
    let formula = Expression::from(r1[2].clone()).one()
        .and(Expression::from(r1[1].clone()).intersection(Expression::from(r1[2].clone()))
             .equals(Expression::from(r1[2].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "When r1[2] is in r1[1], intersection equals r1[2]");

    // one r2[2] && (r2[1] & r2[2] = r2[2])
    let formula = Expression::from(r2[2].clone()).one()
        .and(Expression::from(r2[1].clone()).intersection(Expression::from(r2[2].clone()))
             .equals(Expression::from(r2[2].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "When r2[2] is in r2[1], intersection equals r2[2]");

    // one r3[2] && (r3[1] & r3[2] = r3[2])
    let formula = Expression::from(r3[2].clone()).one()
        .and(Expression::from(r3[1].clone()).intersection(Expression::from(r3[2].clone()))
             .equals(Expression::from(r3[2].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "When r3[2] is in r3[1], intersection equals r3[2]");
}

#[test]
fn test_negated_subset() {
    // Following Java: !(rx3 in rx0)
    // Tests that disjoint relations can fail subset test
    let (bounds, r1, r2, r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // !(r1[3] in r1[0])
    let formula = Expression::from(r1[3].clone())
        .in_set(Expression::from(r1[0].clone()))
        .not();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r1[3] might not be subset of r1[0]");

    // !(r2[3] in r2[0])
    let formula = Expression::from(r2[3].clone())
        .in_set(Expression::from(r2[0].clone()))
        .not();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r2[3] might not be subset of r2[0]");

    // !(r3[3] in r3[0])
    let formula = Expression::from(r3[3].clone())
        .in_set(Expression::from(r3[0].clone()))
        .not();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r3[3] might not be subset of r3[0]");
}

#[test]
fn test_union_subset() {
    // Following Java: some rx0 && (rx1 + rx2 + rx3 in rx0)
    // Tests that union of relations can be subset of universal set
    let (bounds, r1, r2, r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // some r1[0] && (r1[1] + r1[2] + r1[3] in r1[0])
    let union = Expression::from(r1[1].clone())
        .union(Expression::from(r1[2].clone()))
        .union(Expression::from(r1[3].clone()));
    let formula = Expression::from(r1[0].clone()).some()
        .and(union.in_set(Expression::from(r1[0].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "Union of r1 relations can be subset of r1[0]");

    // some r2[0] && (r2[1] + r2[2] + r2[3] in r2[0])
    let union = Expression::from(r2[1].clone())
        .union(Expression::from(r2[2].clone()))
        .union(Expression::from(r2[3].clone()));
    let formula = Expression::from(r2[0].clone()).some()
        .and(union.in_set(Expression::from(r2[0].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "Union of r2 relations can be subset of r2[0]");

    // some r3[0] && (r3[1] + r3[2] + r3[3] in r3[0])
    let union = Expression::from(r3[1].clone())
        .union(Expression::from(r3[2].clone()))
        .union(Expression::from(r3[3].clone()));
    let formula = Expression::from(r3[0].clone()).some()
        .and(union.in_set(Expression::from(r3[0].clone())));
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "Union of r3 relations can be subset of r3[0]");
}

#[test]
fn test_product_equals() {
    // Following Java: some r11 && some r13 && r11->r13 = r21
    // Tests that product can equal another relation
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    let formula = Expression::from(r1[1].clone()).some()
        .and(Expression::from(r1[3].clone()).some())
        .and(Expression::from(r1[1].clone())
             .product(Expression::from(r1[3].clone()))
             .equals(Expression::from(r2[1].clone())));

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "Product r1[1]->r1[3] can equal r2[1]");
}

#[test]
fn test_join_subset() {
    // Following Java: r21.r13 in r11
    // Tests that join result can be subset of another relation
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    let formula = Expression::from(r2[1].clone())
        .join(Expression::from(r1[3].clone()))
        .in_set(Expression::from(r1[1].clone()));

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r2[1].r1[3] can be subset of r1[1]");
}

#[test]
fn test_reflexive_closure_subset() {
    // Following Java: *r22 in r21 + iden
    // Tests reflexive closure subset with IDEN
    let (bounds, _r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    let formula = Expression::from(r2[2].clone())
        .reflexive_closure()
        .in_set(Expression::from(r2[1].clone()).union(Expression::IDEN));

    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "*r2[2] can be subset of r2[1] + IDEN");
}
