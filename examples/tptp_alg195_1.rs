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
// Following Java: kodkod.examples.tptp.ALG195_1

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct ALG195_1 {
    pub e1: [Relation; 7],
    pub e2: [Relation; 7],
    pub h: [Relation; 7],
    pub op1: Relation,
    pub op2: Relation,
    pub s1: Relation,
    pub s2: Relation,
}

impl ALG195_1 {
    pub fn new() -> Self {
        let op1 = Relation::ternary("op1");
        let op2 = Relation::ternary("op2");
        let s1 = Relation::unary("s1");
        let s2 = Relation::unary("s2");

        let e1 = [
            Relation::unary("e10"),
            Relation::unary("e11"),
            Relation::unary("e12"),
            Relation::unary("e13"),
            Relation::unary("e14"),
            Relation::unary("e15"),
            Relation::unary("e16"),
        ];

        let e2 = [
            Relation::unary("e20"),
            Relation::unary("e21"),
            Relation::unary("e22"),
            Relation::unary("e23"),
            Relation::unary("e24"),
            Relation::unary("e25"),
            Relation::unary("e26"),
        ];

        let h = [
            Relation::binary("h1"),
            Relation::binary("h2"),
            Relation::binary("h3"),
            Relation::binary("h4"),
            Relation::binary("h5"),
            Relation::binary("h6"),
            Relation::binary("h7"),
        ];

        ALG195_1 {
            e1,
            e2,
            h,
            op1,
            op2,
            s1,
            s2,
        }
    }

    fn function(s: &Relation, op: &Relation) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let x_expr: Expression = x.clone().into();
        let y_expr: Expression = y.clone().into();
        let s_expr = Expression::from(s.clone());
        let op_expr = Expression::from(op.clone());
        let body = y_expr.join(x_expr.join(op_expr)).one();
        let decls = Decls::from(Decl::one_of(x.clone(), s_expr.clone()))
            .and(Decl::one_of(y.clone(), s_expr.clone()));
        Formula::forall(decls, body)
    }

    /// Returns the relation constraints.
    pub fn decls(&self) -> Formula {
        let mut f = Self::function(&self.s1, &self.op1).and(Self::function(&self.s2, &self.op2));
        for h_rel in &self.h {
            let s1_expr = Expression::from(self.s1.clone());
            let s2_expr = Expression::from(self.s2.clone());
            f = f.and(h_rel.clone().function(s1_expr, s2_expr));
        }
        for i in 0..7 {
            let s1_expr = Expression::from(self.s1.clone());
            let s2_expr = Expression::from(self.s2.clone());
            f = f.and(self.h[i].clone().function(s1_expr, s2_expr));
            f = f.and(Expression::from(self.e1[i].clone()).one());
            f = f.and(Expression::from(self.e2[i].clone()).one());
        }
        f
    }

    /// States that op is a latin square over s = e[0] +...+ e[6].
    fn op_covers_range(e: &[Relation; 7], s: &Relation, op: &Relation) -> Formula {
        let mut f = Formula::TRUE;
        let s_expr = Expression::from(s.clone());
        let op_expr = Expression::from(op.clone());
        for x in e {
            let x_expr = Expression::from(x.clone());
            let left = s_expr.clone().equals(s_expr.clone().join(x_expr.clone().join(op_expr.clone())));
            let right = s_expr.clone().equals(x_expr.join(s_expr.clone().join(op_expr.clone())));
            f = f.and(left).and(right);
        }
        f
    }

    /// Returns axioms 2 and 7.
    pub fn ax2ax7(&self) -> Formula {
        Self::op_covers_range(&self.e1, &self.s1, &self.op1)
    }

    /// Parametrization of axioms 3 and 6.
    fn ax3and6(e: &[Relation; 7], op: &Relation) -> Formula {
        let mut f = Formula::TRUE;
        let op_expr = Expression::from(op.clone());
        for x in e {
            for y in e {
                let x_expr = Expression::from(x.clone());
                let y_expr = Expression::from(y.clone());
                let expr0 = x_expr.clone().join(y_expr.clone().join(op_expr.clone())); // op(y,x)
                let expr1 = y_expr.clone().join(expr0.clone().join(op_expr.clone())); // op(op(y,x),y)
                let expr2 = y_expr.clone().join(expr1.join(op_expr.clone())); // op(op(op(y,x),y),y)
                f = f.and(expr2.equals(x_expr));
            }
        }
        f
    }

    /// Returns axiom 3.
    pub fn ax3(&self) -> Formula {
        Self::ax3and6(&self.e1, &self.op1)
    }

    /// Returns axioms 5 and 8.
    pub fn ax5ax8(&self) -> Formula {
        Self::op_covers_range(&self.e2, &self.s2, &self.op2)
    }

    /// Returns axiom 6.
    pub fn ax6(&self) -> Formula {
        Self::ax3and6(&self.e2, &self.op2)
    }

    /// Parametrization of axioms 12 and 13.
    fn ax12and13(e: &[Relation; 7], op: &Relation) -> Formula {
        let mut f = Formula::TRUE;
        let op_expr = Expression::from(op.clone());
        for r in e {
            let r_expr = Expression::from(r.clone());
            let joined = r_expr.clone().join(r_expr.clone().join(op_expr.clone()));
            f = f.and(joined.equals(r_expr).not());
        }
        f
    }

    /// Returns axiom 12.
    pub fn ax12(&self) -> Formula {
        Self::ax12and13(&self.e1, &self.op1)
    }

    /// Returns axiom 13.
    pub fn ax13(&self) -> Formula {
        Self::ax12and13(&self.e2, &self.op2)
    }

    /// Parametrization of axioms 14 and 15.
    fn ax14and15(e: &[Relation; 7], op: &Relation) -> Formula {
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
        // e1 = op(e5,e5)
        let f1 = Expression::from(e[1].clone()).equals(expr1.clone());
        // e2 = op(op(e5,op(e5,e5)),op(e5,op(e5,e5)))
        let f2 = Expression::from(e[2].clone()).equals(expr3.clone());
        // e3 = op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5)
        let f3 = Expression::from(e[3].clone()).equals(expr4.clone());
        // e4 = op(e5,op(e5,e5))
        let f4 = Expression::from(e[4].clone()).equals(expr2.clone());
        // e6 = op(op(op(op(e5,op(e5,e5)),op(e5,op(e5,e5))),e5),op(e5,op(e5,e5)))
        let f6 = Expression::from(e[6].clone()).equals(expr2.join(expr4.join(op_expr)));

        f0.and(f1).and(f2).and(f3).and(f4).and(f6)
    }

    /// Returns lines 1 and 3-6 of axiom 14.
    pub fn ax14(&self) -> Formula {
        Self::ax14and15(&self.e1, &self.op1)
    }

    /// Returns lines 1 and 3-6 of axiom 15.
    pub fn ax15(&self) -> Formula {
        Self::ax14and15(&self.e2, &self.op2)
    }

    /// Parametrization of axioms 16-22.
    fn ax16_22_single(&self, e: &Relation, h: &Relation) -> Formula {
        let e_expr = Expression::from(e.clone());
        let h_expr = Expression::from(h.clone());
        let op2_expr = Expression::from(self.op2.clone());

        let expr0 = e_expr.clone().join(op2_expr.clone()); // op2(e,...)
        let expr1 = e_expr.clone().join(expr0.clone()); // op2(e,e)
        let expr2 = expr1.clone().join(expr0.clone()); // op2(e,op2(e,e))
        let expr3 = expr2.clone().join(expr2.clone().join(op2_expr.clone())); // op2(op2(e,op2(e,e)),op2(e,op2(e,e)))
        let expr3a = expr3.clone().join(op2_expr.clone()); // op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),...)
        let expr4 = e_expr.clone().join(expr3a.clone()); // op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e)

        // h(e10) = op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),op2(e,op2(e,e)))
        let f0 = Expression::from(self.e1[0].clone()).join(h_expr.clone()).equals(expr2.clone().join(expr3a.clone()));
        // h(e11) = op2(e,e)
        let f1 = Expression::from(self.e1[1].clone()).join(h_expr.clone()).equals(expr1.clone());
        // h(e12) = op2(op2(e,op2(e,e)),op2(e,op2(e,e)))
        let f2 = Expression::from(self.e1[2].clone()).join(h_expr.clone()).equals(expr3.clone());
        // h(e13) = op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e)
        let f3 = Expression::from(self.e1[3].clone()).join(h_expr.clone()).equals(expr4.clone());
        // h(e14) = op2(e,op2(e,e))
        let f4 = Expression::from(self.e1[4].clone()).join(h_expr.clone()).equals(expr2.clone());
        // h1(e15) = e
        let f5 = Expression::from(self.e1[5].clone()).join(h_expr.clone()).equals(e_expr);
        // h(e16) = op2(op2(op2(op2(e,op2(e,e)),op2(e,op2(e,e))),e),op2(e,op2(e,e)))
        let f6 = Expression::from(self.e1[6].clone()).join(h_expr).equals(expr2.join(expr4.join(op2_expr)));

        f0.and(f1).and(f2).and(f3).and(f4).and(f5).and(f6)
    }

    /// Returns axioms 16-22.
    pub fn ax16_22(&self) -> Formula {
        let mut f = Formula::TRUE;
        for i in 0..7 {
            f = f.and(self.ax16_22_single(&self.e2[i], &self.h[i]));
        }
        f
    }

    /// Returns the conjunction of all axioms and implicit constraints (decls()).
    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.ax2ax7())
            .and(self.ax3())
            .and(self.ax5ax8())
            .and(self.ax6())
            .and(self.ax12())
            .and(self.ax13())
            .and(self.ax14())
            .and(self.ax15())
            .and(self.ax16_22())
    }

    /// Returns the part of the conjecture 1 that applies to the given h.
    fn co1h(&self, h: &Relation) -> Formula {
        let mut f = Formula::TRUE;
        let op1_expr = Expression::from(self.op1.clone());
        let op2_expr = Expression::from(self.op2.clone());
        let h_expr = Expression::from(h.clone());

        for x in &self.e1 {
            for y in &self.e1 {
                let x_expr = Expression::from(x.clone());
                let y_expr = Expression::from(y.clone());
                // h(op1(x,y))
                let expr0 = y_expr.clone().join(x_expr.clone().join(op1_expr.clone())).join(h_expr.clone());
                // op2(h(x),h(y))
                let expr1 = y_expr.clone().join(h_expr.clone()).join(x_expr.clone().join(h_expr.clone()).join(op2_expr.clone()));
                f = f.and(expr0.equals(expr1));
            }
        }
        let s1_expr = Expression::from(self.s1.clone());
        let s2_expr = Expression::from(self.s2.clone());
        f.and(s2_expr.equals(s1_expr.join(h_expr)))
    }

    /// Returns conjecture 1.
    pub fn co1(&self) -> Formula {
        let mut f = Formula::FALSE;
        for i in 0..7 {
            f = f.or(self.co1h(&self.h[i]));
        }
        f
    }

    /// Returns the partial bounds the problem (axioms 1, 4, 9-11).
    pub fn bounds(&self) -> Result<Bounds, Box<dyn std::error::Error>> {
        let mut atoms = Vec::new();
        for i in 0..7 {
            atoms.push(format!("e1{i}"));
        }
        for i in 0..7 {
            atoms.push(format!("e2{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let mut b = Bounds::new(u);
        let f = b.universe().factory();

        let s1bound = f.range(f.tuple(&["e10"])?, f.tuple(&["e16"])?)?;
        let s2bound = f.range(f.tuple(&["e20"])?, f.tuple(&["e26"])?)?;

        b.bound_exactly(&self.s1, s1bound.clone())?;
        b.bound_exactly(&self.s2, s2bound.clone())?;

        // axioms 9, 10, 11
        for i in 0..7 {
            b.bound_exactly(&self.e1[i], f.tuple_set(&[&[&format!("e1{i}")]])?)?;
            b.bound_exactly(&self.e2[i], f.tuple_set(&[&[&format!("e2{i}")]])?)?;
        }

        // axiom 1
        let op1_bound = f.area(f.tuple(&["e10", "e10", "e10"])?, f.tuple(&["e16", "e16", "e16"])?)?;
        b.bound(&self.op1, f.none(3), op1_bound)?;

        // axiom 4
        let op2_bound = f.area(f.tuple(&["e20", "e20", "e20"])?, f.tuple(&["e26", "e26", "e26"])?)?;
        b.bound(&self.op2, f.none(3), op2_bound)?;

        let hbound = s1bound.product(&s2bound)?;
        for r in &self.h {
            b.bound(r, f.none(2), hbound.clone())?;
        }

        Ok(b)
    }

    fn display_op(instance: &Instance, op: &Relation) {
        println!("\n{op}:");
        if let Some(tuple_set) = instance.tuples(op) {
            let tuples: Vec<_> = tuple_set.iter().collect();
            for i in 0..7 {
                for j in 0..7 {
                    let idx = i * 7 + j;
                    if idx < tuples.len() {
                        if let Some(atom) = tuples[idx].atom(2) {
                            print!("{:?}\t", atom);
                        }
                    }
                }
                println!();
            }
        }
    }

    /// Prints the values of the op1, op2, and h1-h7 relations to standard out.
    pub fn display(&self, instance: &Instance) {
        Self::display_op(instance, &self.op1);
        Self::display_op(instance, &self.op2);
        for i in 0..7 {
            println!("\n{}:", self.h[i]);
            if let Some(tuple_set) = instance.tuples(&self.h[i]) {
                for tuple in tuple_set.iter() {
                    println!("{:?}", tuple);
                }
            }
        }
    }
}

fn run() {
    let model = ALG195_1::new();
    let options = Options::default();
    let solver = Solver::new(options);

    let f = model.axioms().and(model.co1().not());
    let b = model.bounds().expect("Failed to create bounds");

    match solver.solve(&f, &b) {
        Ok(solution) => {
            if solution.instance().is_none() {
                println!("{:?}", solution);
            } else {
                println!("{:?}", solution.statistics());
                if let Some(instance) = solution.instance() {
                    model.display(instance);
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
fn test_alg195_1_unsatisfiable() {
    // ALG195+1.p should be UNSAT - the axioms contradict the negation of the hypothesis
    run();
}
