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

//! Regression tests for bugs
//!
//! Ported from Java: kodkod.test.unit.RegressionTests (selected tests)

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Bug test: contradiction detection with shared nodes
/// Original: testAleks_03102013
#[test]
fn test_aleks_03102013() {
    // Run multiple times because the bug depends on set ordering
    for _ in 0..10 {
        let r = Relation::unary("R");
        let s = Relation::binary("f");
        let v = Variable::unary("e");
        let decl = Decl::one_of(v.clone(), Expression::from(r.clone()));
        let shared = Expression::from(v).join(Expression::from(s.clone()));

        // expr = all e: R | one ((e.f) - (e.f))
        let expr = Formula::forall(
            Decls::from(decl),
            shared.clone().difference(shared).one()
        );

        // fin = expr AND NOT(expr) - contradiction
        let fin = expr.clone().and(expr.not());

        let universe = Universe::new(&["R$0", "R$1", "R$2"]).unwrap();
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        bounds.bound(&r, factory.none(1), factory.all(1)).unwrap();
        bounds.bound(&s, factory.none(2), factory.all(2)).unwrap();

        let solver = Solver::new(Options::default());
        let solution = solver.solve(&fin, &bounds).unwrap();

        // Should be UNSAT (contradiction)
        assert!(!solution.is_sat(), "Contradiction should be UNSAT");
    }
}

/// Bug test: trivially unsatisfiable formula detection
/// Original: testBGP_03172011
#[test]
fn test_bgp_03172011() {
    let x5 = Relation::unary("s012");
    let x8 = Relation::unary("zero");
    let x9 = Relation::unary("one");
    let x12 = Relation::binary("next");

    let universe = Universe::new(&["0", "1", "2", "3"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    // Exact bounds
    bounds.bound_exactly(&x5, factory.tuple_set(&[&["0"], &["1"], &["2"]]).unwrap()).unwrap();
    bounds.bound_exactly(&x8, factory.tuple_set(&[&["0"]]).unwrap()).unwrap();
    // x9: lower = {1}, upper = {1, 2}
    bounds.bound(&x9,
        factory.tuple_set(&[&["1"]]).unwrap(),
        factory.tuple_set(&[&["1"], &["2"]]).unwrap()
    ).unwrap();
    bounds.bound_exactly(&x12, factory.tuple_set(&[&["1", "2"], &["2", "3"]]).unwrap()).unwrap();

    // Build the complex nested formula
    let x714 = Variable::unary("x714");
    let x713 = Decl::one_of(x714.clone(),
        Expression::from(x8.clone()).union(Expression::from(x9.clone())));

    let x720 = Variable::unary("x720");
    let x723 = Expression::from(x8.clone()).union(Expression::from(x9.clone()));
    let x724 = Expression::from(x9.clone()).join(Expression::from(x12.clone()));
    let x722 = x723.union(x724);
    let x721 = x722.difference(Expression::from(x714.clone()));
    let x719 = Decl::one_of(x720.clone(), x721);

    let x727 = Variable::unary("x727");
    let x732 = Expression::from(x714).union(Expression::from(x720.clone()));
    let x728 = Expression::from(x5).difference(x732);
    let x726 = Decl::one_of(x727.clone(), x728);

    let x735 = Variable::unary("x735");
    let x734 = Decl::one_of(x735, Expression::from(x8));

    let x893 = Variable::unary("x893");
    let x892 = Decl::one_of(x893, Expression::from(x727));
    let x894 = Expression::from(x720).no();
    let x891 = Formula::forall(Decls::from(x892), x894);

    let x712 = Formula::exists(
        Decls::from(x713).and(x719).and(x726).and(x734),
        x891
    );
    let x267 = Formula::FALSE.or(x712);

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&x267, &bounds).unwrap();

    // Should be trivially UNSAT
    assert!(!solution.is_sat(), "Should be unsatisfiable");
}

/// Bug test: N-ary expressions with override
/// Original: testMarceloSimplified_041912
#[test]
fn test_marcelo_simplified_041912() {
    let d2 = Relation::unary("Domain_2");
    let a1 = Relation::unary("Address_1");
    let a2 = Relation::unary("Address_2");
    let a3 = Relation::unary("Address_3");

    let universe = Universe::new(&["a1", "a2", "a3", "d2"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    bounds.bound_exactly(&a1, factory.tuple_set(&[&["a1"]]).unwrap()).unwrap();
    bounds.bound_exactly(&a2, factory.tuple_set(&[&["a2"]]).unwrap()).unwrap();
    bounds.bound_exactly(&a3, factory.tuple_set(&[&["a3"]]).unwrap()).unwrap();
    bounds.bound(&d2, factory.none(1), factory.tuple_set(&[&["d2"]]).unwrap()).unwrap();

    // e = a1 + a2 + a3
    let e = Expression::from(a1.clone())
        .union(Expression::from(a2.clone()))
        .union(Expression::from(a3.clone()));

    // dstBinding = (d2->a1->a3) + (d2->a3->a3)
    let d2_e = Expression::from(d2.clone());
    let a1_e = Expression::from(a1.clone());
    let a3_e = Expression::from(a3.clone());

    let dst_binding = d2_e.clone().product(a1_e.clone()).product(a3_e.clone())
        .union(d2_e.clone().product(a3_e.clone()).product(a3_e.clone()));

    // f = a3 in (e->a1 ++ d2.dstBinding).e
    let f = a3_e.clone().in_set(
        e.clone().product(a1_e)
            .override_with(d2_e.join(dst_binding))
            .join(e)
    );

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&f, &bounds).unwrap();

    // Should be SAT
    assert!(solution.is_sat(), "Should be satisfiable");
}

/// Test for proper handling of set comprehensions
#[test]
fn test_set_comprehension_regression() {
    let r = Relation::unary("R");
    let universe = Universe::new(&["a", "b", "c"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    bounds.bound(&r, factory.none(1), factory.all(1)).unwrap();

    let v = Variable::unary("v");
    let decl = Decl::one_of(v.clone(), Expression::from(r.clone()));

    // { v: R | v in R } should equal R
    let comprehension = Expression::from(v).in_set(Expression::from(r.clone()))
        .comprehension(Decls::from(decl));

    // comprehension = R should be satisfiable
    let f = comprehension.equals(Expression::from(r));

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&f, &bounds).unwrap();

    assert!(solution.is_sat(), "Comprehension should equal its source");
}

/// Test for proper handling of transitive closure
#[test]
fn test_transitive_closure_regression() {
    let r = Relation::binary("R");
    let universe = Universe::new(&["a", "b", "c"]).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    // R = { (a,b), (b,c) }
    let r_val = factory.tuple_set(&[&["a", "b"], &["b", "c"]]).unwrap();
    bounds.bound_exactly(&r, r_val).unwrap();

    // ^R should contain (a,c) as well as original tuples
    // Check: (a,c) in ^R
    let singleton_a = Relation::unary("a");
    let singleton_c = Relation::unary("c");
    bounds.bound_exactly(&singleton_a, factory.tuple_set(&[&["a"]]).unwrap()).unwrap();
    bounds.bound_exactly(&singleton_c, factory.tuple_set(&[&["c"]]).unwrap()).unwrap();

    let closure = Expression::from(r).closure();
    let f = Expression::from(singleton_a).product(Expression::from(singleton_c))
        .in_set(closure);

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&f, &bounds).unwrap();

    // Should be SAT - (a,c) is in ^R
    assert!(solution.is_sat(), "Transitive closure should include (a,c)");
}
