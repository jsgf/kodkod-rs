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

// A KK encoding of NUM378+1.020.015.p from http://www.cs.miami.edu/~tptp/
// Following Java: kodkod.examples.tptp.NUM378

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Solver, Solution, Options};

pub struct NUM378 {
    succ: Relation,
    sum: Relation,
}

impl NUM378 {
    pub fn new() -> Self {
        NUM378 {
            succ: Relation::binary("succ"),
            sum: Relation::ternary("sum"),
        }
    }

    /// Returns the expression y.(x.sum)
    fn sum(&self, x: Expression, y: Expression) -> Expression {
        y.join(x.join(Expression::from(self.sum.clone())))
    }

    /// Returns the successor of x: x.succ
    fn succ(&self, x: Expression) -> Expression {
        x.join(Expression::from(self.succ.clone()))
    }

    /// Returns the predecessor of x: succ.x
    fn pred(&self, x: Expression) -> Expression {
        Expression::from(self.succ.clone()).join(x)
    }

    /// Returns the declarations: one a && one b && one c
    pub fn decls(&self) -> Formula {
        let x = Variable::unary("X");
        let y = Variable::unary("Y");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());

        let sum_one = self.sum(x_expr.clone(), y_expr.clone()).one();

        let decls = Decls::from(Decl::one_of(x, Expression::UNIV))
            .and(Decl::one_of(y, Expression::UNIV));

        self.succ.clone()
            .function(Expression::UNIV, Expression::UNIV)
            .and(Formula::forall(decls, sum_one))
    }

    fn vars(name: &str, size: usize) -> Vec<Variable> {
        (0..size)
            .map(|i| Variable::unary(&format!("{name}{i}")))
            .collect()
    }

    fn build_decls(vars: &[Variable]) -> Decls {
        let mut decls = Decls::from(Decl::one_of(vars[0].clone(), Expression::UNIV));
        for var in &vars[1..] {
            decls = decls.and(Decl::one_of(var.clone(), Expression::UNIV));
        }
        decls
    }

    /// Returns the try_satisfy_this axiom
    pub fn inequalities(&self) -> Formula {
        let x = Self::vars("X", 16);
        let y = Self::vars("Y", 16);
        let npx = Self::vars("NPX", 15);
        let nsx = Self::vars("NSX", 15);
        let npy = Self::vars("NPY", 15);
        let nsy = Self::vars("NSY", 15);

        // Build succ^21
        let mut s21 = Expression::from(self.succ.clone());
        for _ in 1..21 {
            s21 = s21.join(Expression::from(self.succ.clone()));
        }

        let mut f = Formula::TRUE;

        // Build equalities for npx, nsx, npy, nsy
        for i in 0..15 {
            let x_i = Expression::from(x[i].clone());
            let y_i = Expression::from(y[i].clone());
            let npx_i = Expression::from(npx[i].clone());
            let nsx_i = Expression::from(nsx[i].clone());
            let npy_i = Expression::from(npy[i].clone());
            let nsy_i = Expression::from(nsy[i].clone());

            let f0 = npx_i.equals(s21.clone().join(x_i.clone()));
            let f1 = nsx_i.equals(x_i.clone().join(s21.clone()));
            let f2 = npy_i.equals(s21.clone().join(y_i.clone()));
            let f3 = nsy_i.equals(y_i.clone().join(s21.clone()));

            f = f.and(f0).and(f1).and(f2).and(f3);
        }

        // Build recurrence equations
        for i in 1..16 {
            let x_i = Expression::from(x[i].clone());
            let y_i = Expression::from(y[i].clone());
            let x_prev = Expression::from(x[i - 1].clone());
            let y_prev = Expression::from(y[i - 1].clone());
            let npx_prev = Expression::from(npx[i - 1].clone());
            let nsx_prev = Expression::from(nsx[i - 1].clone());
            let npy_prev = Expression::from(npy[i - 1].clone());
            let nsy_prev = Expression::from(nsy[i - 1].clone());

            let f0 = x_i.equals(
                self.sum(
                    self.sum(self.pred(x_prev.clone()), self.succ(y_prev.clone())),
                    self.sum(self.pred(y_prev.clone()), self.succ(x_prev.clone()))
                )
            );

            let f1 = y_i.equals(
                self.sum(
                    self.pred(nsx_prev),
                    self.sum(
                        self.succ(npx_prev),
                        self.sum(self.pred(nsy_prev), self.succ(npy_prev))
                    )
                )
            );

            f = f.and(f0).and(f1);
        }

        // Build disjunction of inequalities for i in 12..16
        let mut g = Formula::FALSE;
        for i in 12..16 {
            let x_i = Expression::from(x[i].clone());
            let y_i = Expression::from(y[i].clone());
            g = g.or(x_i.equals(y_i).not());
        }

        // Build all declarations
        let all_decls = Self::build_decls(&x)
            .and_decls(Self::build_decls(&y))
            .and_decls(Self::build_decls(&npx))
            .and_decls(Self::build_decls(&nsx))
            .and_decls(Self::build_decls(&npy))
            .and_decls(Self::build_decls(&nsy));

        Formula::exists(all_decls, f.and(g))
    }

    /// Returns the conjunction of the axioms and the hypothesis
    pub fn check_inequalities(&self) -> Formula {
        self.decls().and(self.inequalities())
    }

    /// Returns bounds for the problem
    pub fn bounds(&self) -> Bounds {
        let n = 21;
        let mut atoms: Vec<String> = Vec::with_capacity(n + 1);
        atoms.push("goal".to_string());
        for i in 0..n {
            atoms.push(format!("n{i}"));
        }

        let atom_refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_refs).expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let t = b.universe().factory();

        // Build successor relation: n_i -> n_{(i+1) mod n}
        let mut succ_tuples = t.none(2);
        for i in 0..n {
            let from = format!("n{i}");
            let to = format!("n{}", (i + 1) % n);
            succ_tuples.add(t.tuple(&[from.as_str(), to.as_str()]).unwrap()).unwrap();
        }
        b.bound_exactly(&self.succ, succ_tuples).unwrap();

        // Build sum relation: sum(n_i, n_j) = n_{(i+j) mod n}
        let mut sum_tuples = t.none(3);
        for i in 0..n {
            for j in 0..n {
                let a = format!("n{i}");
                let b_atom = format!("n{j}");
                let c = format!("n{}", (i + j) % n);
                sum_tuples.add(t.tuple(&[a.as_str(), b_atom.as_str(), c.as_str()]).unwrap()).unwrap();
            }
        }
        b.bound_exactly(&self.sum, sum_tuples).unwrap();

        b
    }

    pub fn solve(&self) -> Solution {
        let options = Options::default();
        let solver = Solver::new(options);
        let formula = self.check_inequalities();
        let bounds = self.bounds();

        solver.solve(&formula, &bounds).expect("Failed to solve")
    }
}

fn main() {
    let num = NUM378::new();

    println!("Running NUM378...");
    println!("Building bounds...");
    let bounds = num.bounds();
    println!("Bounds created: universe size = {}", bounds.universe().size());

    println!("Building formula...");
    let formula = num.check_inequalities();
    println!("Formula built");

    println!("Solving...");
    let options = Options::default();
    let solver = Solver::new(options);

    eprintln!("DEBUG: About to solve...");
    let sol = solver.solve(&formula, &bounds).expect("Failed to solve");
    eprintln!("DEBUG: Solving complete");

    match sol {
        Solution::Sat { .. } => {
            println!("SATISFIABLE");
        }
        Solution::Unsat { .. } => {
            println!("UNSATISFIABLE");
        }
        Solution::Trivial { is_true, .. } => {
            if is_true {
                println!("Trivially TRUE");
            } else {
                println!("Trivially FALSE");
            }
        }
    }

    println!("\nStatistics: {:?}", sol.statistics());
}
