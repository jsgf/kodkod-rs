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

// Contains the relations/axioms common to the problems ALG195+1.p and ALG197+1.p
// from http://www.cs.miami.edu/~tptp/
// Following Java: kodkod.examples.tptp.Quasigroups7

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Instance, Universe};

/// Contains the relations/axioms common to the problems ALG195+1.p and ALG197+1.p from
/// from http://www.cs.miami.edu/~tptp/
pub struct Quasigroups7 {
    pub e1: [Relation; 7],
    pub e2: [Relation; 7],
    pub h: [Relation; 7],
    pub op1: Relation,
    pub op2: Relation,
    pub s1: Relation,
    pub s2: Relation,
}

impl Quasigroups7 {
    /// Constructs a new instance of Quasigroups7.
    pub fn new() -> Self {
        let op1 = Relation::ternary("op1");
        let op2 = Relation::ternary("op2");
        let s1 = Relation::unary("e1");
        let s2 = Relation::unary("e2");

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

        Quasigroups7 {
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
        let mut formulas = Vec::new();
        formulas.push(Self::function(&self.s1, &self.op1));
        formulas.push(Self::function(&self.s2, &self.op2));
        for h_rel in &self.h {
            let s1_expr = Expression::from(self.s1.clone());
            let s2_expr = Expression::from(self.s2.clone());
            formulas.push(h_rel.clone().function(s1_expr, s2_expr));
        }
        Formula::and_all(formulas)
    }

    fn op1(&self, arg1: Expression, arg2: Expression) -> Expression {
        arg1.join(arg2.join(Expression::from(self.op1.clone())))
    }

    fn op2(&self, arg1: Expression, arg2: Expression) -> Expression {
        arg1.join(arg2.join(Expression::from(self.op2.clone())))
    }

    /// Returns axioms 2 and 7.
    pub fn ax2ax7(&self) -> Formula {
        let x = Variable::unary("x");
        let x_expr: Expression = x.clone().into();
        let s1_expr = Expression::from(self.s1.clone());
        let body = s1_expr.clone()
            .equals(self.op1(x_expr.clone(), s1_expr.clone()))
            .and(s1_expr.clone().equals(self.op1(s1_expr.clone(), x_expr)));
        let decls = Decls::from(Decl::one_of(x, s1_expr));
        Formula::forall(decls, body)
    }

    /// Returns axiom 3.
    pub fn ax3(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let x_expr: Expression = x.clone().into();
        let y_expr: Expression = y.clone().into();
        let s1_expr = Expression::from(self.s1.clone());
        let inner = self.op1(y_expr.clone(), x_expr.clone());
        let middle = self.op1(inner, y_expr.clone());
        let outer = self.op1(middle, y_expr.clone());
        let body = x_expr.equals(outer);
        let decls = Decls::from(Decl::one_of(x, s1_expr.clone()))
            .and(Decl::one_of(y, s1_expr));
        Formula::forall(decls, body)
    }

    /// Returns axioms 5 and 8.
    pub fn ax5ax8(&self) -> Formula {
        let x = Variable::unary("x");
        let x_expr: Expression = x.clone().into();
        let s2_expr = Expression::from(self.s2.clone());
        let body = s2_expr.clone()
            .equals(self.op2(x_expr.clone(), s2_expr.clone()))
            .and(s2_expr.clone().equals(self.op2(s2_expr.clone(), x_expr)));
        let decls = Decls::from(Decl::one_of(x, s2_expr));
        Formula::forall(decls, body)
    }

    /// Returns axiom 6.
    pub fn ax6(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let x_expr: Expression = x.clone().into();
        let y_expr: Expression = y.clone().into();
        let s2_expr = Expression::from(self.s2.clone());
        let inner = self.op2(y_expr.clone(), x_expr.clone());
        let middle = self.op2(inner, y_expr.clone());
        let outer = self.op2(middle, y_expr.clone());
        let body = x_expr.equals(outer);
        let decls = Decls::from(Decl::one_of(x, s2_expr.clone()))
            .and(Decl::one_of(y, s2_expr));
        Formula::forall(decls, body)
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

        b.bound_exactly(&self.s1, f.range(f.tuple(&["e10"])?, f.tuple(&["e16"])?)?)?;
        b.bound_exactly(&self.s2, f.range(f.tuple(&["e20"])?, f.tuple(&["e26"])?)?)?;

        // axioms 9, 10, 11
        for i in 0..7 {
            b.bound_exactly(&self.e1[i], f.tuple_set(&[&[&format!("e1{i}")]])?)?;
            b.bound_exactly(&self.e2[i], f.tuple_set(&[&[&format!("e2{i}")]])?)?;
        }

        // axiom 1
        let op1h = f.area(f.tuple(&["e10", "e10", "e10"])?, f.tuple(&["e16", "e16", "e16"])?)?;
        // axiom 4
        let op2h = f.area(f.tuple(&["e20", "e20", "e20"])?, f.tuple(&["e26", "e26", "e26"])?)?;

        b.bound(&self.op1, f.none(3), op1h)?;
        b.bound(&self.op2, f.none(3), op2h)?;

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

    /// Returns the part of the conjecture 1 that applies to the given h.
    fn co1h(&self, h: &Relation) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let x_expr: Expression = x.clone().into();
        let y_expr: Expression = y.clone().into();
        let s1_expr = Expression::from(self.s1.clone());
        let h_expr = Expression::from(h.clone());
        let left = self.op1(x_expr.clone(), y_expr.clone()).join(h_expr.clone());
        let right = self.op2(x_expr.clone().join(h_expr.clone()), y_expr.clone().join(h_expr));
        let body = left.equals(right);
        let decls = Decls::from(Decl::one_of(x, s1_expr.clone()))
            .and(Decl::one_of(y, s1_expr));
        Formula::forall(decls, body)
    }

    /// Returns conjecture 1.
    pub fn co1(&self) -> Formula {
        let formulas: Vec<Formula> = self.h.iter().map(|h| self.co1h(h)).collect();
        Formula::or_all(formulas)
    }
}

/// Trait for TPTP problems that extend Quasigroups7
pub trait Quasigroups7Ext {
    fn base(&self) -> &Quasigroups7;

    /// Parametrization of axioms 12 and 13.
    fn ax12and13(&self, e: &[Relation; 7], op: &Relation) -> Formula;

    /// Returns axiom 12.
    fn ax12(&self) -> Formula {
        let base = self.base();
        self.ax12and13(&base.e1, &base.op1)
    }

    /// Returns axiom 13.
    fn ax13(&self) -> Formula {
        let base = self.base();
        self.ax12and13(&base.e2, &base.op2)
    }

    /// Parametrization of axioms 14 and 15.
    fn ax14and15(&self, e: &[Relation; 7], op: &Relation) -> Formula;

    /// Returns lines 1 and 3-6 of axiom 14.
    fn ax14(&self) -> Formula {
        let base = self.base();
        self.ax14and15(&base.e1, &base.op1)
    }

    /// Returns lines 1 and 3-6 of axiom 15.
    fn ax15(&self) -> Formula {
        let base = self.base();
        self.ax14and15(&base.e2, &base.op2)
    }

    /// Parametrization of axioms 16-22.
    fn ax16_22_single(&self, e: &Relation, h: &Relation) -> Formula;

    /// Returns lines 2-7 of axioms 16-22.
    fn ax16_22(&self) -> Formula {
        let base = self.base();
        let formulas: Vec<Formula> = (0..7)
            .map(|i| self.ax16_22_single(&base.e2[i], &base.h[i]))
            .collect();
        Formula::and_all(formulas)
    }

    /// Returns the conjunction of all axioms and implicit constraints (decls()).
    fn axioms(&self) -> Formula {
        let base = self.base();
        let formulas = vec![
            base.decls(),
            base.ax2ax7(),
            base.ax3(),
            base.ax5ax8(),
            base.ax6(),
            self.ax12(),
            self.ax13(),
            self.ax14(),
            self.ax15(),
            self.ax16_22(),
        ];
        Formula::and_all(formulas)
    }
}

fn main() {
    println!("Quasigroups7 is a base module for TPTP problems ALG195 and ALG197.");
    println!("Use the specific problem examples (e.g., tptp_alg195) to run tests.");
}
