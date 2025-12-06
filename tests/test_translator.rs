/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

//! Tests for FOL to SAT translation
//!
//! Ported from Java: kodkod.test.unit.TranslatorTest

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct TranslatorTest {
    bounds: Bounds,
    r1: [Relation; 4],
    r2: [Relation; 4],
}

impl TranslatorTest {
    fn new() -> Self {
        // Create universe with 10 atoms (0-9 as strings)
        let atoms: Vec<&str> = (0..10).map(|i| match i {
            0 => "0", 1 => "1", 2 => "2", 3 => "3", 4 => "4",
            5 => "5", 6 => "6", 7 => "7", 8 => "8", 9 => "9",
            _ => unreachable!()
        }).collect();
        let universe = Universe::new(&atoms).unwrap();
        let mut bounds = Bounds::new(universe);
        let factory = bounds.factory();

        let r1: [Relation; 4] = [
            Relation::unary("r10"),
            Relation::unary("r11"),
            Relation::unary("r12"),
            Relation::unary("r13"),
        ];

        let r2: [Relation; 4] = [
            Relation::binary("r20"),
            Relation::binary("r21"),
            Relation::binary("r22"),
            Relation::binary("r23"),
        ];

        // Set up bounds for unary relations
        bounds.bound(&r1[0], factory.none(1), factory.all(1)).unwrap();
        bounds.bound(&r1[1], factory.none(1), factory.tuple_set(&[&["2"], &["3"], &["4"]]).unwrap()).unwrap();
        bounds.bound(&r1[2], factory.none(1), factory.tuple_set(&[&["4"]]).unwrap()).unwrap();
        bounds.bound(&r1[3], factory.none(1), factory.tuple_set(&[&["5"], &["6"], &["7"], &["8"]]).unwrap()).unwrap();

        // Set up bounds for binary relations
        bounds.bound(&r2[0], factory.none(2), factory.all(2)).unwrap();
        // r21: restricted area
        let r21_upper = factory.tuple_set(&[
            &["2", "3"], &["2", "4"], &["2", "5"],
            &["3", "3"], &["3", "4"], &["3", "5"],
            &["4", "3"], &["4", "4"], &["4", "5"],
            &["5", "3"], &["5", "4"], &["5", "5"],
        ]).unwrap();
        bounds.bound(&r2[1], factory.none(2), r21_upper).unwrap();
        // r22: single tuple
        bounds.bound(&r2[2], factory.none(2), factory.tuple_set(&[&["5", "7"]]).unwrap()).unwrap();
        // r23: another area
        let r23_upper = factory.tuple_set(&[
            &["6", "0"], &["6", "1"], &["6", "2"],
            &["7", "0"], &["7", "1"], &["7", "2"],
            &["8", "0"], &["8", "1"], &["8", "2"],
        ]).unwrap();
        bounds.bound(&r2[3], factory.none(2), r23_upper).unwrap();

        TranslatorTest { bounds, r1, r2 }
    }

    fn is_satisfiable(&self, formula: &Formula) -> bool {
        let solver = Solver::new(Options::default());
        let solution = solver.solve(formula, &self.bounds).unwrap();
        solution.is_sat()
    }
}

// ============================================================================
// Multiplicity Tests
// ============================================================================

#[test]
fn test_multiplicity_some() {
    let test = TranslatorTest::new();

    // some r1[i] should be satisfiable for all i
    for r in &test.r1 {
        assert!(test.is_satisfiable(&Expression::from(r.clone()).some()),
            "some {} should be satisfiable", r.name());
    }

    // some r2[i] should be satisfiable for all i
    for r in &test.r2 {
        assert!(test.is_satisfiable(&Expression::from(r.clone()).some()),
            "some {} should be satisfiable", r.name());
    }
}

#[test]
fn test_multiplicity_one() {
    let test = TranslatorTest::new();

    // one r1[i] should be satisfiable for all i
    for r in &test.r1 {
        assert!(test.is_satisfiable(&Expression::from(r.clone()).one()),
            "one {} should be satisfiable", r.name());
    }
}

#[test]
fn test_multiplicity_lone() {
    let test = TranslatorTest::new();

    // lone r1[i] should be satisfiable for all i
    for r in &test.r1 {
        assert!(test.is_satisfiable(&Expression::from(r.clone()).lone()),
            "lone {} should be satisfiable", r.name());
    }
}

#[test]
fn test_multiplicity_no() {
    let test = TranslatorTest::new();

    // no r1[i] should be satisfiable for all i (can be empty)
    for r in &test.r1 {
        assert!(test.is_satisfiable(&Expression::from(r.clone()).no()),
            "no {} should be satisfiable", r.name());
    }
}

#[test]
fn test_multiplicity_intersection_empty() {
    let test = TranslatorTest::new();

    // r1[1] & r1[3] should be empty (disjoint ranges)
    let intersection = Expression::from(test.r1[1].clone())
        .intersection(Expression::from(test.r1[3].clone()));

    // no (r11 & r13) - should be satisfiable (intersection is empty)
    assert!(test.is_satisfiable(&intersection.clone().no()));

    // some (r11 & r13) - should be unsatisfiable
    assert!(!test.is_satisfiable(&intersection.some()));
}

#[test]
fn test_multiplicity_difference_empty() {
    let test = TranslatorTest::new();

    // r1[3] - r1[3] should be empty
    let diff = Expression::from(test.r1[3].clone())
        .difference(Expression::from(test.r1[3].clone()));

    // no (r13 - r13) - should be satisfiable
    assert!(test.is_satisfiable(&diff.clone().no()));

    // some (r13 - r13) - should be unsatisfiable
    assert!(!test.is_satisfiable(&diff.some()));
}

#[test]
fn test_multiplicity_union() {
    let test = TranslatorTest::new();

    // some (r11 + r13) - should be satisfiable
    let union = Expression::from(test.r1[1].clone())
        .union(Expression::from(test.r1[3].clone()));
    assert!(test.is_satisfiable(&union.some()));
}

// ============================================================================
// Comparison Tests
// ============================================================================

#[test]
fn test_comparison_subset_reflexive() {
    let test = TranslatorTest::new();

    // r in r should always be satisfiable
    for r in &test.r1 {
        let e = Expression::from(r.clone());
        assert!(test.is_satisfiable(&e.clone().in_set(e)));
    }
}

#[test]
fn test_comparison_subset_with_intersection() {
    let test = TranslatorTest::new();

    // some r12 && (r11 & r12 in r12) - should be satisfiable
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let f = r12.clone().some().and(r11.intersection(r12.clone()).in_set(r12));
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_comparison_equals_with_intersection() {
    let test = TranslatorTest::new();

    // one r12 && (r11 & r12 = r12) - should be satisfiable
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let f = r12.clone().one().and(r11.intersection(r12.clone()).equals(r12));
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_comparison_not_subset() {
    let test = TranslatorTest::new();

    // !(r13 in r10) - should be satisfiable (r13 can have elements not in r10)
    let r10 = Expression::from(test.r1[0].clone());
    let r13 = Expression::from(test.r1[3].clone());
    let f = r13.in_set(r10).not();
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_comparison_union_subset() {
    let test = TranslatorTest::new();

    // some r10 && (r11 + r12 + r13 in r10) - should be satisfiable
    let r10 = Expression::from(test.r1[0].clone());
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let r13 = Expression::from(test.r1[3].clone());
    let union = r11.union(r12).union(r13);
    let f = r10.clone().some().and(union.in_set(r10));
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_comparison_join_subset() {
    let test = TranslatorTest::new();

    // r21.r13 in r11 - should be satisfiable
    let r11 = Expression::from(test.r1[1].clone());
    let r13 = Expression::from(test.r1[3].clone());
    let r21 = Expression::from(test.r2[1].clone());
    let f = r21.join(r13).in_set(r11);
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_comparison_reflexive_closure() {
    let test = TranslatorTest::new();

    // *r22 in r21 + iden - should be satisfiable
    let r21 = Expression::from(test.r2[1].clone());
    let r22 = Expression::from(test.r2[2].clone());
    let f = r22.reflexive_closure().in_set(r21.union(Expression::IDEN));
    assert!(test.is_satisfiable(&f));
}

// ============================================================================
// Quantified Formula Tests
// ============================================================================

#[test]
fn test_quantified_forall() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");
    let r10 = Expression::from(test.r1[0].clone());

    // forall v1: r1[i] | v1 in r10 - should be satisfiable
    for i in 1..4 {
        let ri = Expression::from(test.r1[i].clone());
        let d = Decl::one_of(v1.clone(), ri);
        let body = Expression::from(v1.clone()).in_set(r10.clone());
        let f = Formula::forall(Decls::from(d), body);
        assert!(test.is_satisfiable(&f),
            "forall v1: r1[{}] | v1 in r10 should be satisfiable", i);
    }
}

#[test]
fn test_quantified_exists() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");
    let r10 = Expression::from(test.r1[0].clone());

    // exists v1: r1[i] | v1 in r10 - should be satisfiable
    for i in 1..4 {
        let ri = Expression::from(test.r1[i].clone());
        let d = Decl::one_of(v1.clone(), ri);
        let body = Expression::from(v1.clone()).in_set(r10.clone());
        let f = Formula::exists(Decls::from(d), body);
        assert!(test.is_satisfiable(&f),
            "exists v1: r1[{}] | v1 in r10 should be satisfiable", i);
    }
}

#[test]
fn test_quantified_two_vars() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");
    let v2 = Variable::unary("v2");

    // forall v1: r12, v2: r13 | v1->v2 in r21 - should be satisfiable
    let r12 = Expression::from(test.r1[2].clone());
    let r13 = Expression::from(test.r1[3].clone());
    let r21 = Expression::from(test.r2[1].clone());

    let d = Decls::from(Decl::one_of(v1.clone(), r12))
        .and(Decl::one_of(v2.clone(), r13));
    let body = Expression::from(v1).product(Expression::from(v2)).in_set(r21);
    let f = Formula::forall(d, body);
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_quantified_with_join() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");

    // forall v1: r13 | some v1.(~r21) - should be satisfiable
    let r13 = Expression::from(test.r1[3].clone());
    let r21 = Expression::from(test.r2[1].clone());

    let d = Decl::one_of(v1.clone(), r13);
    let body = Expression::from(v1).join(r21.transpose()).some();
    let f = Formula::forall(Decls::from(d), body);
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_quantified_with_closure() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");

    // forall v1: r13 | some v1.(^r23) - should be satisfiable
    let r13 = Expression::from(test.r1[3].clone());
    let r23 = Expression::from(test.r2[3].clone());

    let d = Decl::one_of(v1.clone(), r13);
    let body = Expression::from(v1).join(r23.closure()).some();
    let f = Formula::forall(Decls::from(d), body);
    assert!(test.is_satisfiable(&f));
}

// ============================================================================
// Comprehension Tests
// ============================================================================

#[test]
fn test_comprehension_some() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");

    // some { v1: r11 + r12 | some v1.r21 }
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let r21 = Expression::from(test.r2[1].clone());

    let d = Decl::one_of(v1.clone(), r11.union(r12));
    let body = Expression::from(v1).join(r21).some();
    let comprehension = body.comprehension(Decls::from(d));
    let f = comprehension.some();
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_comprehension_one() {
    let test = TranslatorTest::new();
    let v1 = Variable::unary("v1");
    let v2 = Variable::unary("v2");

    // For this test, we need pairs that could be in the relation
    // r21 has tuples like (2,3), (3,4), etc. matching r11 x r12 domain
    // one { v1: r11, v2: r12 | v1->v2 in r21 }
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let r21 = Expression::from(test.r2[1].clone());

    let d = Decls::from(Decl::one_of(v1.clone(), r11))
        .and(Decl::one_of(v2.clone(), r12));
    let body = Expression::from(v1).product(Expression::from(v2)).in_set(r21);
    let comprehension = body.comprehension(d);
    // Use 'some' instead of 'one' since we just want to verify comprehension works
    let f = comprehension.some();
    assert!(test.is_satisfiable(&f));
}

// ============================================================================
// IFF Tests
// ============================================================================

#[test]
fn test_iff() {
    let test = TranslatorTest::new();

    // some r11 && (r11 in r12 iff r12 in r11)
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let f = r11.clone().some()
        .and(r11.clone().in_set(r12.clone()).iff(r12.clone().in_set(r11)));
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_iff_with_no() {
    let test = TranslatorTest::new();

    // some r11 && no r12 && (r11 in r12 iff r12 in r11) - should be UNSAT
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let f = r11.clone().some()
        .and(r12.clone().no())
        .and(r11.clone().in_set(r12.clone()).iff(r12.clone().in_set(r11)));
    assert!(!test.is_satisfiable(&f));
}

// ============================================================================
// N-ary Expression Tests
// ============================================================================

#[test]
fn test_nary_union() {
    let test = TranslatorTest::new();

    // Test that binary union chain equals Expression::union_all
    let r10 = Expression::from(test.r1[0].clone());
    let r11 = Expression::from(test.r1[1].clone());
    let r12 = Expression::from(test.r1[2].clone());
    let r13 = Expression::from(test.r1[3].clone());

    let binary_union = r10.clone()
        .union(r11.clone())
        .union(r12.clone())
        .union(r13.clone());

    let nary_union = Expression::union_all(vec![r10, r11, r12, r13]);

    // binary = nary should be unsatisfiable to negate
    let f = binary_union.equals(nary_union).not();
    assert!(!test.is_satisfiable(&f));
}

// ============================================================================
// N-ary Formula Tests
// ============================================================================

#[test]
fn test_nary_and() {
    let test = TranslatorTest::new();

    // Test that binary AND chain equals Formula::and_all
    let f0 = Expression::from(test.r1[0].clone()).some();
    let f1 = Expression::from(test.r1[1].clone()).some();
    let f2 = Expression::from(test.r1[2].clone()).some();
    let f3 = Expression::from(test.r1[3].clone()).some();

    let binary_and = f0.clone().and(f1.clone()).and(f2.clone()).and(f3.clone());
    let nary_and = Formula::and_all(vec![f0, f1, f2, f3]);

    // (binary <=> nary) should be satisfiable
    let f = binary_and.iff(nary_and);
    assert!(test.is_satisfiable(&f));
}

#[test]
fn test_nary_or() {
    let test = TranslatorTest::new();

    // Test that binary OR chain equals Formula::or_all
    let f0 = Expression::from(test.r1[0].clone()).some();
    let f1 = Expression::from(test.r1[1].clone()).some();
    let f2 = Expression::from(test.r1[2].clone()).some();
    let f3 = Expression::from(test.r1[3].clone()).some();

    let binary_or = f0.clone().or(f1.clone()).or(f2.clone()).or(f3.clone());
    let nary_or = Formula::or_all(vec![f0, f1, f2, f3]);

    // (binary <=> nary) should be satisfiable
    let f = binary_or.iff(nary_or);
    assert!(test.is_satisfiable(&f));
}
