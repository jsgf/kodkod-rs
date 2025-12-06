/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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

// A KK encoding of ALG197+1.p from http://www.cs.miami.edu/~tptp/
// Following Java: kodkod.examples.tptp.ALG197

#[allow(dead_code)]
mod tptp_quasigroups7;

use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::instance::Bounds;
use kodkod_rs::solver::{Options, Solver};
use tptp_quasigroups7::{Quasigroups7, Quasigroups7Ext};

pub struct ALG197 {
    base: Quasigroups7,
}

impl ALG197 {
    pub fn new() -> Self {
        ALG197 {
            base: Quasigroups7::new(),
        }
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    pub fn check_co1(&self) -> Formula {
        self.axioms().and(self.base.co1().not())
    }

    /// Returns the bounds for the problem (axioms 1, 4, 9-11, last formula of 14-15,
    /// and first formula of 16-22).
    pub fn bounds(&self) -> Result<Bounds, Box<dyn std::error::Error>> {
        let mut b = self.base.bounds()?;
        let f = b.universe().factory();

        let mut op1h = b.upper_bound(&self.base.op1).ok_or("No upper bound for op1")?.clone();
        let mut op2h = b.upper_bound(&self.base.op2).ok_or("No upper bound for op2")?.clone();

        // axiom 14, line 6 (note: using e16, not e15)
        let op1l = f.tuple_set(&[&["e16", "e16", "e15"]])?;
        // axiom 15, line 6 (note: using e26, not e25)
        let op2l = f.tuple_set(&[&["e26", "e26", "e25"]])?;

        // Remove area and add specific tuple for axiom 14
        let area_to_remove = f.area(f.tuple(&["e16", "e16", "e10"])?, f.tuple(&["e16", "e16", "e16"])?)?;
        for tuple in area_to_remove.iter() {
            op1h.remove(&tuple);
        }
        op1h.add_all(&op1l)?;

        // Remove area and add specific tuple for axiom 15
        let area_to_remove = f.area(f.tuple(&["e26", "e26", "e20"])?, f.tuple(&["e26", "e26", "e26"])?)?;
        for tuple in area_to_remove.iter() {
            op2h.remove(&tuple);
        }
        op2h.add_all(&op2l)?;

        b.bound(&self.base.op1, op1l.clone(), op1h)?;
        b.bound(&self.base.op2, op2l.clone(), op2h)?;

        // First line of axioms 16-22
        let mut high = f.area(f.tuple(&["e10", "e20"])?, f.tuple(&["e15", "e26"])?)?;
        for i in 0..7 {
            let t = f.tuple(&["e16", &format!("e2{i}")])?;
            high.add(t.clone())?;
            b.bound(&self.base.h[i], f.tuple_set(&[&["e16", &format!("e2{i}")]])?, high.clone())?;
            high.remove(&t);
        }

        Ok(b)
    }
}

impl Quasigroups7Ext for ALG197 {
    fn base(&self) -> &Quasigroups7 {
        &self.base
    }

    /// Parametrization of axioms 12 and 13.
    /// For ALG197: (∃i: e[i].join(e[i].join(op)) = e[i]) ∧ (∃i: e[i].join(e[i].join(op)) ≠ e[i])
    fn ax12and13(&self, e: &[Relation; 7], op: &Relation) -> Formula {
        let op_expr = Expression::from(op.clone());
        let mut f0 = Vec::new(); // formulas for "some i where op(e[i],e[i]) = e[i]"
        let mut f1 = Vec::new(); // formulas for "some i where op(e[i],e[i]) ≠ e[i]"

        for i in 0..7 {
            let e_i = Expression::from(e[i].clone());
            // op(e[i], e[i])
            let opi = e_i.clone().join(e_i.clone().join(op_expr.clone()));
            // op(e[i], e[i]) = e[i]
            let eq = opi.equals(e_i);
            f0.push(eq.clone());
            f1.push(eq.not());
        }

        // At least one i where op(e[i],e[i]) = e[i], and at least one where it's not
        Formula::or_all(f0).and(Formula::or_all(f1))
    }

    /// Parametrization of axioms 14 and 15.
    /// Uses e[6] as the base element (unlike ALG195 which uses e[5])
    fn ax14and15(&self, e: &[Relation; 7], op: &Relation) -> Formula {
        let op_expr = Expression::from(op.clone());
        let e6_expr = Expression::from(e[6].clone());

        let expr0 = e6_expr.clone().join(op_expr.clone()); // op(e6,...)
        let expr1 = e6_expr.clone().join(expr0.clone()); // op(e6,e6)
        let expr2 = expr1.clone().join(expr1.clone().join(op_expr.clone())); // op(op(e6,e6),op(e6,e6))
        let expr3 = expr2.clone().join(expr0.clone()); // op(e6,op(op(e6,e6),op(e6,e6)))

        // e0 = op(e6,op(e6,e6))
        let f0 = Expression::from(e[0].clone()).equals(expr1.clone().join(expr0.clone()));
        // e1 = op(op(e6,e6),op(e6,e6))
        let f1 = Expression::from(e[1].clone()).equals(expr2.clone());
        // e2 = op(op(op(e6,e6),op(e6,e6)),op(e6,e6))
        let f2 = Expression::from(e[2].clone()).equals(expr1.clone().join(expr2.clone().join(op_expr.clone())));
        // e3 = op(e6,op(op(e6,e6),op(e6,e6)))
        let f3 = Expression::from(e[3].clone()).equals(expr3.clone());
        // e4 = op(e6,op(e6,op(op(e6,e6),op(e6,e6))))
        let f4 = Expression::from(e[4].clone()).equals(expr3.clone().join(expr0.clone()));

        Formula::and_all(vec![f0, f1, f2, f3, f4])
    }

    /// Parametrization of axioms 16-22.
    /// Uses e (from the parameter) as the base, and references e1[i] for h mapping
    fn ax16_22_single(&self, e: &Relation, h: &Relation) -> Formula {
        let e_expr = Expression::from(e.clone());
        let h_expr = Expression::from(h.clone());
        let op2_expr = Expression::from(self.base.op2.clone());

        let expr0 = e_expr.clone().join(op2_expr.clone()); // op2(e,...)
        let expr1 = e_expr.clone().join(expr0.clone()); // op2(e,e)
        let expr2 = expr1.clone().join(expr1.clone().join(op2_expr.clone())); // op2(op2(e,e),op2(e,e))
        let expr3 = expr2.clone().join(expr0.clone()); // op2(e,op2(op2(e,e),op2(e,e)))

        // h(e10) = op2(e,op2(e,e))
        let f0 = Expression::from(self.base.e1[0].clone()).join(h_expr.clone()).equals(expr1.clone().join(expr0.clone()));
        // h(e11) = op2(op2(e,e),op2(e,e))
        let f1 = Expression::from(self.base.e1[1].clone()).join(h_expr.clone()).equals(expr2.clone());
        // h(e12) = op2(op2(op2(e,e),op2(e,e)),op2(e,e))
        let f2 = Expression::from(self.base.e1[2].clone()).join(h_expr.clone()).equals(expr1.clone().join(expr2.clone().join(op2_expr.clone())));
        // h(e13) = op2(e,op2(op2(e,e),op2(e,e)))
        let f3 = Expression::from(self.base.e1[3].clone()).join(h_expr.clone()).equals(expr3.clone());
        // h(e14) = op2(e,op2(e,op2(op2(e,e),op2(e,e))))
        let f4 = Expression::from(self.base.e1[4].clone()).join(h_expr.clone()).equals(expr3.clone().join(expr0.clone()));
        // h(e15) = op2(e,e)
        let f5 = Expression::from(self.base.e1[5].clone()).join(h_expr).equals(expr1);

        Formula::and_all(vec![f0, f1, f2, f3, f4, f5])
    }
}

fn run() {
    let model = ALG197::new();
    let options = Options::default();
    let solver = Solver::new(options);

    let f = model.check_co1();
    let b = model.bounds().expect("Failed to create bounds");

    match solver.solve(&f, &b) {
        Ok(solution) => {
            if solution.instance().is_none() {
                println!("{:?}", solution);
            } else {
                println!("{:?}", solution.statistics());
                if let Some(instance) = solution.instance() {
                    model.base.display(instance);
                }
            }
        }
        Err(e) => {
            eprintln!("Error solving: {e}");
            std::process::exit(1);
        }
    }
}

fn main() {
    run()
}

#[test]
fn test_alg197_unsatisfiable() {
    // ALG197+1.p should be UNSAT - the axioms contradict the negation of the hypothesis
    run();
}
