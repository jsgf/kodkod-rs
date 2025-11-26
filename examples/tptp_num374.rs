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

// A KK encoding of NUM374+1.p from http://www.cs.miami.edu/~tptp/
// Following Java: kodkod.examples.tptp.NUM374

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Solver, Solution, Options};

pub struct NUM374 {
    sum: Relation,
    product: Relation,
    exponent: Relation,
    n1: Relation,
}

impl NUM374 {
    pub fn new() -> Self {
        NUM374 {
            n1: Relation::unary("n1"),
            sum: Relation::ternary("sum"),
            product: Relation::ternary("product"),
            exponent: Relation::ternary("exponent"),
        }
    }

    /// Returns op[X][Y].
    fn apply(&self, op: &Relation, x: Expression, y: Expression) -> Expression {
        y.join(x.join(Expression::from(op.clone())))
    }

    /// Returns sum[X][Y].
    fn sum(&self, x: Expression, y: Expression) -> Expression {
        self.apply(&self.sum, x, y)
    }

    /// Returns product[X][Y].
    fn product(&self, x: Expression, y: Expression) -> Expression {
        self.apply(&self.product, x, y)
    }

    /// Returns exponent[X][Y].
    fn exponent(&self, x: Expression, y: Expression) -> Expression {
        self.apply(&self.exponent, x, y)
    }

    /// Returns the declarations.
    pub fn decls(&self) -> Formula {
        let f0 = Expression::from(self.n1.clone()).one();
        let x = Variable::unary("X");
        let y = Variable::unary("Y");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());

        let f1 = Formula::and_all(vec![
            self.sum(x_expr.clone(), y_expr.clone()).one(),
            self.product(x_expr.clone(), y_expr.clone()).one(),
            self.exponent(x_expr.clone(), y_expr.clone()).one(),
        ]);

        let decls = Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
            .and(Decl::one_of(y, Expression::UNIV));
        f0.and(Formula::forall(decls, f1))
    }

    /// Returns all X, Y: Num | op[X][Y] = op[Y][X]
    fn symmetric(&self, op: &Relation) -> Formula {
        let x = Variable::unary("X");
        let y = Variable::unary("Y");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());

        let lhs = self.apply(op, x_expr.clone(), y_expr.clone());
        let rhs = self.apply(op, y_expr.clone(), x_expr.clone());

        let decls = Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
            .and(Decl::one_of(y, Expression::UNIV));
        Formula::forall(decls, lhs.equals(rhs))
    }

    /// Returns all X, Y, Z: Num | op[X][op[Y][Z]] = op[op[X][Y]][Z]
    fn associative(&self, op: &Relation) -> Formula {
        let x = Variable::unary("X");
        let y = Variable::unary("Y");
        let z = Variable::unary("Z");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());
        let z_expr = Expression::from(z.clone());

        let yz = self.apply(op, y_expr.clone(), z_expr.clone());
        let xy = self.apply(op, x_expr.clone(), y_expr.clone());

        let lhs = self.apply(op, x_expr.clone(), yz);
        let rhs = self.apply(op, xy, z_expr.clone());

        let decls = Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
            .and(Decl::one_of(y.clone(), Expression::UNIV))
            .and(Decl::one_of(z, Expression::UNIV));

        Formula::forall(decls, lhs.equals(rhs))
    }

    /// Returns the sum_symmetry axiom.
    pub fn sum_symmetry(&self) -> Formula {
        self.symmetric(&self.sum)
    }

    /// Returns the sum_associativity axiom.
    pub fn sum_associativity(&self) -> Formula {
        self.associative(&self.sum)
    }

    /// Returns the product_identity axiom.
    pub fn product_identity(&self) -> Formula {
        // ! [X] : product(X,n1) = X
        let x = Variable::unary("X");
        let x_expr = Expression::from(x.clone());
        let n1_expr = Expression::from(self.n1.clone());

        let decls = Decls::from(Decl::one_of(x, Expression::UNIV));
        Formula::forall(
            decls,
            self.product(x_expr.clone(), n1_expr).equals(x_expr.clone())
        )
    }

    /// Returns the product_symmetry axiom.
    pub fn product_symmetry(&self) -> Formula {
        self.symmetric(&self.product)
    }

    /// Returns the product_associativity axiom.
    pub fn product_associativity(&self) -> Formula {
        self.associative(&self.product)
    }

    /// Returns the sum_product_distribution axiom.
    pub fn sum_product_distribution(&self) -> Formula {
        // ! [X,Y,Z] : product(X,sum(Y,Z)) = sum(product(X,Y),product(X,Z))
        let x = Variable::unary("X");
        let y = Variable::unary("Y");
        let z = Variable::unary("Z");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());
        let z_expr = Expression::from(z.clone());

        let yz_sum = self.sum(y_expr.clone(), z_expr.clone());
        let lhs = self.product(x_expr.clone(), yz_sum);

        let xy_prod = self.product(x_expr.clone(), y_expr.clone());
        let xz_prod = self.product(x_expr.clone(), z_expr.clone());
        let rhs = self.sum(xy_prod, xz_prod);

        let decls = Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
            .and(Decl::one_of(y.clone(), Expression::UNIV))
            .and(Decl::one_of(z, Expression::UNIV));

        Formula::forall(decls, lhs.equals(rhs))
    }

    /// Returns the exponent_n1 axiom.
    pub fn exponent_n1(&self) -> Formula {
        // ! [X] : exponent(n1,X) = n1
        let x = Variable::unary("X");
        let x_expr = Expression::from(x.clone());
        let n1_expr = Expression::from(self.n1.clone());

        let decls = Decls::from(Decl::one_of(x, Expression::UNIV));
        Formula::forall(
            decls,
            self.exponent(n1_expr.clone(), x_expr).equals(n1_expr.clone())
        )
    }

    /// Returns the exponent_identity axiom.
    pub fn exponent_identity(&self) -> Formula {
        // ! [X] : exponent(X,n1) = X
        let x = Variable::unary("X");
        let x_expr = Expression::from(x.clone());
        let n1_expr = Expression::from(self.n1.clone());

        let decls = Decls::from(Decl::one_of(x, Expression::UNIV));
        Formula::forall(
            decls,
            self.exponent(x_expr.clone(), n1_expr).equals(x_expr.clone())
        )
    }

    /// Returns the exponent_sum_product axiom.
    pub fn exponent_sum_product(&self) -> Formula {
        // ! [X,Y,Z] : exponent(X,sum(Y,Z)) = product(exponent(X,Y),exponent(X,Z))
        let x = Variable::unary("X");
        let y = Variable::unary("Y");
        let z = Variable::unary("Z");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());
        let z_expr = Expression::from(z.clone());

        let yz_sum = self.sum(y_expr.clone(), z_expr.clone());
        let lhs = self.exponent(x_expr.clone(), yz_sum);

        let xy_exp = self.exponent(x_expr.clone(), y_expr.clone());
        let xz_exp = self.exponent(x_expr.clone(), z_expr.clone());
        let rhs = self.product(xy_exp, xz_exp);

        let decls = Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
            .and(Decl::one_of(y.clone(), Expression::UNIV))
            .and(Decl::one_of(z, Expression::UNIV));

        Formula::forall(decls, lhs.equals(rhs))
    }

    /// Returns the exponent_product_distribution axiom.
    pub fn exponent_product_distribution(&self) -> Formula {
        // ! [X,Y,Z] : exponent(product(X,Y),Z) = product(exponent(X,Z),exponent(Y,Z))
        let x = Variable::unary("X");
        let y = Variable::unary("Y");
        let z = Variable::unary("Z");

        let x_expr = Expression::from(x.clone());
        let y_expr = Expression::from(y.clone());
        let z_expr = Expression::from(z.clone());

        let xy_prod = self.product(x_expr.clone(), y_expr.clone());
        let lhs = self.exponent(xy_prod, z_expr.clone());

        let xz_exp = self.exponent(x_expr.clone(), z_expr.clone());
        let yz_exp = self.exponent(y_expr.clone(), z_expr.clone());
        let rhs = self.product(xz_exp, yz_exp);

        let decls = Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
            .and(Decl::one_of(y.clone(), Expression::UNIV))
            .and(Decl::one_of(z, Expression::UNIV));

        Formula::forall(decls, lhs.equals(rhs))
    }

    /// Returns the co1 conjecture.
    pub fn co1(&self) -> Formula {
        // ! [X,Y] : product(X,Y) = product(Y,X)
        self.product_symmetry()
    }

    /// Returns all the axioms.
    pub fn axioms(&self) -> Formula {
        Formula::and_all(vec![
            self.decls(),
            self.sum_symmetry(),
            self.sum_associativity(),
            self.product_identity(),
            self.product_associativity(),
            self.sum_product_distribution(),
            self.exponent_n1(),
            self.exponent_identity(),
            self.exponent_sum_product(),
            self.exponent_product_distribution(),
        ])
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    pub fn check_co1(&self) -> Formula {
        self.axioms().and(self.co1().not())
    }

    /// Returns the bounds for the given universe size.
    pub fn bounds(&self, size: usize) -> Bounds {
        let atoms: Vec<&str> = (0..size).map(|i| Box::leak(Box::new(i.to_string())).as_str()).collect();
        let u = Universe::new(&atoms).expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let t = b.universe().factory();

        // Set n1 to atom "0"
        b.bound_exactly(&self.n1, t.tuple_set(&[&["0"]]).unwrap()).unwrap();

        // Set all operations as ternary relations over entire universe
        let all = t.all(1);
        let all3 = all.product(&all).unwrap().product(&all).unwrap();

        b.bound(&self.sum, t.none(3), all3.clone()).unwrap();
        b.bound(&self.product, t.none(3), all3.clone()).unwrap();
        b.bound(&self.exponent, t.none(3), all3).unwrap();

        b
    }

    pub fn solve(&self, size: usize) -> Solution {
        let options = Options::default();
        let solver = Solver::new(options);
        let formula = self.check_co1();
        let bounds = self.bounds(size);

        solver.solve(&formula, &bounds).expect("Failed to solve")
    }
}

fn main() {
    let num = NUM374::new();

    println!("Running NUM374 with universe size 3...");
    let sol = num.solve(3);

    match sol {
        Solution::Sat { .. } => {
            println!("SATISFIABLE - Found counterexample to product commutativity");
            println!("(This means product doesn't have to be commutative given the other axioms)");
        }
        Solution::Unsat { .. } => {
            println!("UNSATISFIABLE - Product must be commutative");
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