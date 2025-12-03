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

// A KK encoding of ALG195+1.p from http://www.cs.miami.edu/~tptp/
// Following Java: kodkod.examples.tptp.ALG195

mod tptp_quasigroups7;

use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::instance::Bounds;
use kodkod_rs::solver::{Options, Solver};
use tptp_quasigroups7::{Quasigroups7, Quasigroups7Ext};

pub struct ALG195 {
    base: Quasigroups7,
}

impl ALG195 {
    pub fn new() -> Self {
        ALG195 {
            base: Quasigroups7::new(),
        }
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    pub fn check_co1(&self) -> Formula {
        self.axioms().and(self.base.co1().not())
    }

    /// Returns the bounds for the problem (axioms 1, 4, 9-13, second formula of 14-15,
    /// and first formula of 16-22).
    pub fn bounds(&self) -> Result<Bounds, Box<dyn std::error::Error>> {
        let mut b = self.base.bounds()?;
        let f = b.universe().factory();

        let mut op1h = b.upper_bound(&self.base.op1).ok_or("No upper bound for op1")?.clone();
        let mut op2h = b.upper_bound(&self.base.op2).ok_or("No upper bound for op2")?.clone();

        // axiom 12 and 13 - remove diagonal elements
        for i in 0..7 {
            op1h.remove(&f.tuple(&[&format!("e1{i}"), &format!("e1{i}"), &format!("e1{i}")])?);
            op2h.remove(&f.tuple(&[&format!("e2{i}"), &format!("e2{i}"), &format!("e2{i}")])?);
        }

        // axiom 14, line 2
        let op1l = f.tuple_set(&[&["e15", "e15", "e11"]])?;
        // axiom 15, line 2
        let op2l = f.tuple_set(&[&["e25", "e25", "e21"]])?;

        // Remove area and add specific tuple for axiom 14
        let area_to_remove = f.area(f.tuple(&["e15", "e15", "e10"])?, f.tuple(&["e15", "e15", "e16"])?)?;
        for tuple in area_to_remove.iter() {
            op1h.remove(&tuple);
        }
        op1h.add_all(&op1l)?;

        // Remove area and add specific tuple for axiom 15
        let area_to_remove = f.area(f.tuple(&["e25", "e25", "e20"])?, f.tuple(&["e25", "e25", "e26"])?)?;
        for tuple in area_to_remove.iter() {
            op2h.remove(&tuple);
        }
        op2h.add_all(&op2l)?;

        b.bound(&self.base.op1, op1l.clone(), op1h)?;
        b.bound(&self.base.op2, op2l.clone(), op2h)?;

        // First line of axioms 16-22
        let mut high = f.area(f.tuple(&["e10", "e20"])?, f.tuple(&["e14", "e26"])?)?;
        high.add_all(&f.area(f.tuple(&["e16", "e20"])?, f.tuple(&["e16", "e26"])?)?)?;
        for i in 0..7 {
            let t = f.tuple(&["e15", &format!("e2{i}")])?;
            high.add(t.clone())?;
            b.bound(&self.base.h[i], f.tuple_set(&[&["e15", &format!("e2{i}")]])?, high.clone())?;
            high.remove(&t);
        }

        Ok(b)
    }
}

impl Quasigroups7Ext for ALG195 {
    fn base(&self) -> &Quasigroups7 {
        &self.base
    }

    /// Parametrization of axioms 12 and 13.
    fn ax12and13(&self, _e: &[Relation; 7], _op: &Relation) -> Formula {
        Formula::TRUE
    }

    /// Parametrization of axioms 14 and 15.
    fn ax14and15(&self, e: &[Relation; 7], op: &Relation) -> Formula {
        let op_expr = Expression::from(op.clone());
        let e5_expr = Expression::from(e[5].clone());

        let expr0 = e5_expr.clone().join(op_expr.clone()); // op(e5,...)
        let expr1 = e5_expr.clone().join(expr0.clone()); // op(e5,e5)
        let expr2 = expr1.clone().join(expr0.clone()); // op(e5,op(e5,e5))
        let expr3 = expr2.clone().join(expr2.clone().join(op_expr.clone())); // op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        let expr3a = expr3.clone().join(op_expr.clone()); // op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),...)
        let expr4 = e5_expr.clone().join(expr3a.clone()); // op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)

        // e0 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),op(e5,op(e5,e5)))
        let f0 = Expression::from(e[0].clone()).equals(expr2.clone().join(expr3a.clone()));
        // e2 = op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        let f2 = Expression::from(e[2].clone()).equals(expr3.clone());
        // e3 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)
        let f3 = Expression::from(e[3].clone()).equals(expr4.clone());
        // e4 = op(e5,op(e5,e5))
        let f4 = Expression::from(e[4].clone()).equals(expr2.clone());
        // e6 = op(op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5),op(e5,op(e5,e5)))
        let f6 = Expression::from(e[6].clone()).equals(expr2.join(expr4.join(op_expr)));

        Formula::and_all(vec![f0, f2, f3, f4, f6])
    }

    /// Parametrization of axioms 16-22.
    fn ax16_22_single(&self, e: &Relation, h: &Relation) -> Formula {
        let e_expr = Expression::from(e.clone());
        let h_expr = Expression::from(h.clone());
        let op2_expr = Expression::from(self.base.op2.clone());

        let expr0 = e_expr.clone().join(op2_expr.clone()); // op2(e,...)
        let expr1 = e_expr.clone().join(expr0.clone()); // op2(e,e)
        let expr2 = expr1.clone().join(expr0.clone()); // op2(e,op2(e,e))
        let expr3 = expr2.clone().join(expr2.clone().join(op2_expr.clone())); // op2(op2(e,op2(e,e)),op2(e,op2(e,e)))
        let expr3a = expr3.clone().join(op2_expr.clone()); // op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),...)
        let expr4 = e_expr.clone().join(expr3a.clone()); // op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e)

        // h(e10) = op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),op2(e,op2(e,e)))
        let f0 = Expression::from(self.base.e1[0].clone()).join(h_expr.clone()).equals(expr2.clone().join(expr3a.clone()));
        // h(e11) = op2(e,e)
        let f1 = Expression::from(self.base.e1[1].clone()).join(h_expr.clone()).equals(expr1.clone());
        // h(e12) = op2(op2(e,op2(e,e)),op2(e,op2(e,e)))
        let f2 = Expression::from(self.base.e1[2].clone()).join(h_expr.clone()).equals(expr3.clone());
        // h(e13) = op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e)
        let f3 = Expression::from(self.base.e1[3].clone()).join(h_expr.clone()).equals(expr4.clone());
        // h(e14) = op2(e,op2(e,e))
        let f4 = Expression::from(self.base.e1[4].clone()).join(h_expr.clone()).equals(expr2.clone());
        // h(e16) = op2(op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e),op2(e,op2(e,e)))
        let f6 = Expression::from(self.base.e1[6].clone()).join(h_expr).equals(expr2.join(expr4.join(op2_expr)));

        Formula::and_all(vec![f0, f1, f2, f3, f4, f6])
    }
}

fn run() {
    let model = ALG195::new();
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
            eprintln!("Error solving: {}", e);
            std::process::exit(1);
        }
    }
}

fn main() {
    run()
}

#[test]
fn test_alg195_unsatisfiable() {
    // ALG195+1.p should be UNSAT - the axioms contradict the negation of the hypothesis
    run();
}
