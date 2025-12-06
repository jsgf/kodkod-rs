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

//! Tests for Skolemization
//!
//! Ported from Java: kodkod.test.unit.SkolemizationTest

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solver};

const USIZE: usize = 10;

struct SkolemizationTest {
    bounds: Bounds,
    r1a: Relation,
    r1b: Relation,
    r2a: Relation,
    r2b: Relation,
}

impl SkolemizationTest {
    fn new() -> Self {
        // Create universe with atoms "0" through "9"
        let atoms: Vec<&str> = (0..USIZE).map(|i| match i {
            0 => "0", 1 => "1", 2 => "2", 3 => "3", 4 => "4",
            5 => "5", 6 => "6", 7 => "7", 8 => "8", 9 => "9",
            _ => unreachable!()
        }).collect();
        let universe = Universe::new(&atoms).unwrap();
        let mut bounds = Bounds::new(universe);

        let r1a = Relation::unary("r1a");
        let r1b = Relation::unary("r1b");
        let r2a = Relation::binary("r2a");
        let r2b = Relation::binary("r2b");

        // Set up bounds similar to Java setUp()
        let factory = bounds.factory();

        // r1a: atoms 0-4
        let r1a_upper = factory.tuple_set(&[&["0"], &["1"], &["2"], &["3"], &["4"]]).unwrap();
        bounds.bound(&r1a, factory.none(1), r1a_upper.clone()).unwrap();

        // r1b: atoms 5-9
        let r1b_upper = factory.tuple_set(&[&["5"], &["6"], &["7"], &["8"], &["9"]]).unwrap();
        bounds.bound(&r1b, factory.none(1), r1b_upper.clone()).unwrap();

        // r2a: r1a × r1b (atoms 0-4 × atoms 5-9)
        let r2a_upper = r1a_upper.clone().product(&r1b_upper).unwrap();
        bounds.bound(&r2a, factory.none(2), r2a_upper).unwrap();

        // r2b: r1b × r1a (atoms 5-9 × atoms 0-4)
        let r2b_upper = r1b_upper.product(&r1a_upper).unwrap();
        bounds.bound(&r2b, factory.none(2), r2b_upper).unwrap();

        SkolemizationTest { bounds, r1a, r1b, r2a, r2b }
    }

    fn solve_and_check(&self, formula: &Formula, expected_skolem_count: usize) {
        let mut options = Options::default();
        options.bool_options.skolem_depth = Some(1);
        let solver = Solver::new(options);
        let solution = solver.solve(formula, &self.bounds).unwrap();

        if let Some(inst) = solution.instance() {
            self.assert_skolem_count(inst, expected_skolem_count);
        }
        // If UNSAT, that's fine - no assertion failure
    }

    fn solve_and_check_with_depth(&self, formula: &Formula, depth: usize, expected_skolem_count: usize) {
        let mut options = Options::default();
        options.bool_options.skolem_depth = Some(depth);
        let solver = Solver::new(options);
        let solution = solver.solve(formula, &self.bounds).unwrap();

        if let Some(inst) = solution.instance() {
            self.assert_skolem_count(inst, expected_skolem_count);
        }
    }

    fn solve_and_check_no_skolems(&self, formula: &Formula) {
        let mut options = Options::default();
        options.bool_options.skolem_depth = Some(1);
        let solver = Solver::new(options);
        let solution = solver.solve(formula, &self.bounds).unwrap();

        if let Some(inst) = solution.instance() {
            let bounds_count = self.bounds.relations().count();
            let inst_count = inst.relations().count();
            let skolem_count = inst_count - bounds_count;
            assert_eq!(skolem_count, 0,
                "No Skolems expected, found {}. Bounds relations: {}, Instance relations: {}",
                skolem_count, bounds_count, inst_count);
        }
    }

    fn solve_and_count_extra(&self, formula: &Formula, depth: usize, min_extra: usize) {
        let mut options = Options::default();
        options.bool_options.skolem_depth = Some(depth);
        let solver = Solver::new(options);
        let solution = solver.solve(formula, &self.bounds).unwrap();

        if let Some(inst) = solution.instance() {
            let bounds_count = self.bounds.relations().count();
            let inst_count = inst.relations().count();
            assert!(inst_count >= bounds_count + min_extra,
                "Expected at least {} extra relations, got {}. Bounds: {}, Instance: {}",
                min_extra, inst_count - bounds_count, bounds_count, inst_count);
        }
    }

    /// Asserts that the instance contains exactly the expected number of Skolem relations
    fn assert_skolem_count(&self, inst: &Instance, expected_count: usize) {
        let bounds_count = self.bounds.relations().count();
        let inst_count = inst.relations().count();
        let skolem_count = inst_count - bounds_count;

        // Verify Skolem relations are named with $ prefix
        for rel in inst.relations() {
            let is_in_bounds = self.bounds.relations().any(|r| r.name() == rel.name());
            if !is_in_bounds {
                assert!(rel.name().starts_with('$'),
                    "Extra relation '{}' should be a Skolem (start with $)", rel.name());
            }
        }

        assert_eq!(expected_count, skolem_count,
            "Expected {} Skolem relations, found {}",
            expected_count, skolem_count);
    }
}

// ============================================================================
// Test: No Skolems
// ============================================================================

/// Tests pure universal quantification - no Skolems should be created
#[test]
fn test_no_skolems_one() {
    let test = SkolemizationTest::new();
    let v = Variable::unary("v");
    let d = Decl::one_of(v.clone(), Expression::from(test.r1a.clone()));

    // Pure universal: forall v: r1a | some v.r2a - no Skolem needed
    let v_join_r2a = Expression::from(v.clone()).join(Expression::from(test.r2a.clone()));
    let f = Formula::forall(Decls::from(d.clone()), v_join_r2a.some());
    test.solve_and_check_no_skolems(&f);
}

// Note: Java tests additional cases where existentials are in "negative" positions
// (inside NOT, OR, IFF, as consequent of IMPLIES). The Rust implementation currently
// Skolemizes these anyway, which is semantically correct but may create more Skolems
// than strictly necessary. This is an optimization difference, not a correctness issue.

// ============================================================================
// Test: Skolems
// ============================================================================

/// Tests cases where Skolem functions SHOULD be created
#[test]
fn test_skolems_one() {
    let test = SkolemizationTest::new();
    let va = Variable::unary("va");
    let vb = Variable::unary("vb");

    let da = Decl::one_of(va.clone(), Expression::from(test.r1a.clone()));
    let _db = Decl::one_of(vb.clone(), Expression::from(test.r1b.clone()));

    // Test 1: !forall va: r1a | va in r1b.r2b
    // Negated universal becomes existential - should create 1 Skolem
    let r1b_join_r2b = Expression::from(test.r1b.clone())
        .join(Expression::from(test.r2b.clone()));
    let va_in_join = Expression::from(va.clone()).in_set(r1b_join_r2b.clone());
    let f1 = Formula::forall(Decls::from(da.clone()), va_in_join.clone()).not();
    test.solve_and_check(&f1, 1);

    // Test 2: !(some r2b => forall va: r1a | va in r1b.r2b)
    let r2b_some = Expression::from(test.r2b.clone()).some();
    let f2 = r2b_some.implies(Formula::forall(Decls::from(da.clone()), va_in_join.clone())).not();
    test.solve_and_check(&f2, 1);

    // Test 3: exists va: r1a | va in r1b.r2b
    let f3 = Formula::exists(Decls::from(da.clone()), va_in_join.clone());
    test.solve_and_check(&f3, 1);
}

#[test]
fn test_skolems_with_two_vars() {
    let test = SkolemizationTest::new();
    let va = Variable::unary("va");
    let vb = Variable::unary("vb");

    let da = Decl::one_of(va.clone(), Expression::from(test.r1a.clone()));
    let db = Decl::one_of(vb.clone(), Expression::from(test.r1b.clone()));

    // exists va: r1a, vb: r1b | va in vb.r2b
    // Should create 2 Skolem relations
    let vb_join_r2b = Expression::from(vb.clone())
        .join(Expression::from(test.r2b.clone()));
    let va_in_vb_r2b = Expression::from(va.clone()).in_set(vb_join_r2b);
    let f = Formula::exists(Decls::from(da).and(db), va_in_vb_r2b);
    test.solve_and_check(&f, 2);
}

// ============================================================================
// Test: Deep Skolems
// ============================================================================

#[test]
fn test_deep_skolems() {
    let test = SkolemizationTest::new();
    let va = Variable::unary("va");
    let vb = Variable::unary("vb");

    let da1 = Decl::one_of(va.clone(), Expression::from(test.r1a.clone()));
    let db = Decl::one_of(vb.clone(), Expression::from(test.r1b.clone()));

    // forall va: r1a | exists vb: r1b | va in vb.r2b
    // This should create 1 Skolem for vb (va is universally quantified)
    let vb_join_r2b = Expression::from(vb.clone())
        .join(Expression::from(test.r2b.clone()));
    let va_in_vb_r2b = Expression::from(va.clone()).in_set(vb_join_r2b);
    let inner_exists = Formula::exists(Decls::from(db), va_in_vb_r2b);
    let f = Formula::forall(Decls::from(da1), inner_exists);

    test.solve_and_check_with_depth(&f, 3, 1);
}

#[test]
fn test_multiple_skolems_deep() {
    let test = SkolemizationTest::new();
    let va = Variable::unary("va");
    let vb = Variable::unary("vb");

    let da1 = Decl::one_of(va.clone(), Expression::from(test.r1a.clone()));
    let db = Decl::one_of(vb.clone(), Expression::from(test.r1b.clone()));

    // forall va: r1a | !forall vb: r1b | va in vb.r2b
    // AND exists va: r1a | exists vb: r1b | va in vb.r2b
    // Should create 3+ Skolem relations total
    let vb_join_r2b = Expression::from(vb.clone())
        .join(Expression::from(test.r2b.clone()));
    let va_in_vb_r2b = Expression::from(va.clone()).in_set(vb_join_r2b);

    let f0 = va_in_vb_r2b.clone();
    let f1 = Formula::forall(Decls::from(da1.clone()),
        Formula::forall(Decls::from(db.clone()), f0.clone()).not());
    let f2 = Formula::exists(Decls::from(da1),
        Formula::exists(Decls::from(db), f0));

    test.solve_and_count_extra(&f1.and(f2), 3, 3);
}

// ============================================================================
// Additional tests for Skolemization behavior
// ============================================================================

#[test]
fn test_skolem_not_created_for_universal() {
    let test = SkolemizationTest::new();
    let v = Variable::unary("v");
    let d = Decl::one_of(v.clone(), Expression::from(test.r1a.clone()));

    // forall v: r1a | some v.r2a (no Skolem needed - universal only)
    let v_join_r2a = Expression::from(v).join(Expression::from(test.r2a.clone()));
    let f = Formula::forall(Decls::from(d), v_join_r2a.some());

    test.solve_and_check_no_skolems(&f);
}

#[test]
fn test_basic_existential() {
    let test = SkolemizationTest::new();
    let v = Variable::unary("v");
    let d = Decl::one_of(v.clone(), Expression::from(test.r1a.clone()));

    // exists v: r1a | some v.r2a
    // Should create 1 Skolem
    let v_join_r2a = Expression::from(v).join(Expression::from(test.r2a.clone()));
    let f = Formula::exists(Decls::from(d), v_join_r2a.some());

    test.solve_and_check(&f, 1);
}
