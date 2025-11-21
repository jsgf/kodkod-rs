//! Translator tests for multiplicity formulas
//!
//! Following Java: kodkod.test.unit.TranslatorTest
//! Tests that multiplicity formulas (no, lone, one, some) translate correctly

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

    // r1[1]: range from 2 to (1,4)
    let lower = factory.none(1);
    let upper = factory.range(
        factory.tuple(&["2"]).unwrap(),
        factory.tuple(&["4"]).unwrap()
    ).unwrap();
    bounds.bound(&r1[1], lower, upper).unwrap();

    // r1[2]: exactly (1,4)
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

    // r2[2]: exactly (2,5)
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

    // r3[2]: exactly (3,3,4)
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
fn test_multiplicity_no() {
    // Following Java: testTranslateMultiplicityFormula_NO
    // NO means the set is empty
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // All relations can be NO (empty), except those with exact bounds
    for i in 0..4 {
        if i != 2 {  // Skip r1[2], r2[2], r3[2] which are exactly bounded
            let formula = Expression::from(r1[i].clone()).no();
            let result = solver.solve(&formula, &bounds).unwrap();
            assert!(result.is_sat(), "r1[{i}].no() should be SAT");

            let formula = Expression::from(r2[i].clone()).no();
            let result = solver.solve(&formula, &bounds).unwrap();
            assert!(result.is_sat(), "r2[{i}].no() should be SAT");
        }
    }

    // no (rx1 & rx3) should be SAT (disjoint ranges can be empty intersection)
    let formula = Expression::from(r1[1].clone()).intersection(Expression::from(r1[3].clone())).no();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "no (r1[1] & r1[3]) should be SAT");

    // no (rx3 - rx3) should be SAT (difference of set with itself is empty)
    let formula = Expression::from(r1[3].clone()).difference(Expression::from(r1[3].clone())).no();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "no (r1[3] - r1[3]) should be SAT");
}

#[test]
fn test_multiplicity_some() {
    // Following Java: testTranslateMultiplicityFormula_SOME
    // SOME means the set is non-empty
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // All relations can be SOME (non-empty)
    for i in 0..4 {
        let formula = Expression::from(r1[i].clone()).some();
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r1[{i}].some() should be SAT");

        let formula = Expression::from(r2[i].clone()).some();
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r2[{i}].some() should be SAT");
    }

    // some (rx1 + rx3) should be SAT (union can be non-empty)
    let formula = Expression::from(r1[1].clone()).union(Expression::from(r1[3].clone())).some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "some (r1[1] + r1[3]) should be SAT");

    // some r21.r13 should be SAT (join can be non-empty)
    let formula = Expression::from(r2[1].clone()).join(Expression::from(r1[3].clone())).some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "some (r2[1].r1[3]) should be SAT");

    // some ^r21 (closure) should be SAT
    let formula = Expression::from(r2[1].clone()).closure().some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "some (^r2[1]) should be SAT");

    // some ~r23 (transpose) should be SAT
    let formula = Expression::from(r2[3].clone()).transpose().some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "some (~r2[3]) should be SAT");
}

#[test]
fn test_multiplicity_one() {
    // Following Java: testTranslateMultiplicityFormula_ONE
    // ONE means the set has exactly one element
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // All relations can be ONE (singleton)
    for i in 0..4 {
        let formula = Expression::from(r1[i].clone()).one();
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r1[{i}].one() should be SAT");

        let formula = Expression::from(r2[i].clone()).one();
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r2[{i}].one() should be SAT");
    }

    // r1[2] is exactly bound to one element, so it must be ONE
    let formula = Expression::from(r1[2].clone()).one();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat());
    let instance = result.instance().unwrap();
    let tuples = instance.tuples(&r1[2]);
    let count = tuples.iter().count();
    assert_eq!(count, 1, "r1[2] should have exactly 1 tuple");
}

#[test]
fn test_multiplicity_lone() {
    // Following Java: testTranslateMultiplicityFormula_LONE
    // LONE means the set has at most one element (0 or 1)
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // All relations can be LONE (0 or 1 element)
    for i in 0..4 {
        let formula = Expression::from(r1[i].clone()).lone();
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r1[{i}].lone() should be SAT");

        let formula = Expression::from(r2[i].clone()).lone();
        let result = solver.solve(&formula, &bounds).unwrap();
        assert!(result.is_sat(), "r2[{i}].lone() should be SAT");
    }

    // r1[2] is exactly bound to one element, so it must be LONE
    let formula = Expression::from(r1[2].clone()).lone();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat());
}

#[test]
fn test_intersection_multiplicity() {
    // Test that intersection of two relations with overlapping bounds
    // can satisfy multiplicity constraints
    let (bounds, r1, r2, _r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // r1[1] and r1[2] have overlapping ranges (both include 4)
    // so their intersection can be SOME
    let formula = Expression::from(r1[1].clone()).intersection(Expression::from(r1[2].clone())).some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r1[1] & r1[2] should have non-empty intersection");

    // r2[1] and r2[2] have overlapping ranges (both include (2,5))
    // so their intersection can be SOME
    let formula = Expression::from(r2[1].clone()).intersection(Expression::from(r2[2].clone())).some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "r2[1] & r2[2] should have non-empty intersection");
}

#[test]
fn test_product_intersection_multiplicity() {
    // Test product and intersection operations with multiplicity
    let (bounds, r1, r2, r3) = create_test_bounds();
    let solver = Solver::new(Options::default());

    // (r11 x r13) & r21 can be non-empty
    // This tests that product followed by intersection works
    let product = Expression::from(r1[1].clone()).product(Expression::from(r1[3].clone()));
    let intersection = product.intersection(Expression::from(r2[1].clone()));
    let formula = intersection.some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "(r1[1] x r1[3]) & r2[1] can be non-empty");

    // (r11 x r21) & r31 can be non-empty
    let product = Expression::from(r1[1].clone()).product(Expression::from(r2[1].clone()));
    let intersection = product.intersection(Expression::from(r3[1].clone()));
    let formula = intersection.some();
    let result = solver.solve(&formula, &bounds).unwrap();
    assert!(result.is_sat(), "(r1[1] x r2[1]) & r3[1] can be non-empty");
}
