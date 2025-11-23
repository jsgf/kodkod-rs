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

//! A Kodkod encoding of the Latin squares problem.

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{atom_as_str, Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Model of a Latin square
struct LatinSquare {
    square: Relation,
}

impl LatinSquare {
    /// Constructs a model of a Latin square
    fn new() -> Self {
        Self {
            square: Relation::ternary("square"),
        }
    }

    /// Returns a Kodkod encoding of the qg5 problem
    /// (http://4c.ucc.ie/~tw/csplib/prob/prob003/spec.html)
    ///
    /// Constraint: ((b*a)*b)*b = a
    fn qg5(&self) -> Formula {
        let a = Variable::unary("a");
        let b = Variable::unary("b");

        // b*a
        let e0 = Expression::from(a.clone()).join(
            Expression::from(b.clone()).join(Expression::from(self.square.clone()))
        );

        // (b*a)*b
        let e1 = Expression::from(b.clone()).join(e0.join(Expression::from(self.square.clone())));

        // ((b*a)*b)*b
        let e2 = Expression::from(b.clone()).join(e1.join(Expression::from(self.square.clone())));

        let body = e2.intersection(Expression::from(a.clone())).some();
        let decls = Decls::from(Decl::one_of(a, Expression::UNIV))
            .and(Decl::one_of(b, Expression::UNIV));

        Formula::forall(decls, body)
    }

    /// Returns a formula stating that the square relation is a latin square
    fn latin(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");

        // For all x, y: exactly one z such that (x, y, z) is in square
        let body0 = Expression::from(y.clone())
            .join(Expression::from(x.clone()).join(Expression::from(self.square.clone())))
            .one();
        let decls0 = Decls::from(Decl::one_of(x, Expression::UNIV))
            .and(Decl::one_of(y, Expression::UNIV));
        let f0 = Formula::forall(decls0, body0);

        let z = Variable::unary("z");

        // Each row contains all elements
        let row = Expression::UNIV.in_set(
            Expression::UNIV.join(Expression::from(z.clone()).join(Expression::from(self.square.clone())))
        );

        // Each column contains all elements
        let col = Expression::UNIV.in_set(
            Expression::from(z.clone()).join(Expression::UNIV.join(Expression::from(self.square.clone())))
        );

        let body1 = row.and(col);
        let decls1 = Decls::from(Decl::one_of(z, Expression::UNIV));

        f0.and(Formula::forall(decls1, body1))
    }

    /// Returns a formula stating that the square relation is idempotent
    ///
    /// For all x: (x, x, x) is in square
    fn idempotent(&self) -> Formula {
        let x = Variable::unary("x");
        let body = Expression::from(x.clone())
            .product(Expression::from(x.clone()))
            .product(Expression::from(x.clone()))
            .in_set(Expression::from(self.square.clone()));
        let decls = Decls::from(Decl::one_of(x, Expression::UNIV));

        Formula::forall(decls, body)
    }

    /// Returns the bounds for a Latin square of the given order
    fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let nums: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        let universe = Universe::new(&nums.iter().map(|s| s.as_str()).collect::<Vec<_>>())?;
        let factory = universe.factory();

        let mut bounds = Bounds::new(universe);
        bounds.bound(&self.square, factory.none(3), factory.all(3))?;

        Ok(bounds)
    }
}

fn usage() {
    eprintln!("Usage: csp_latin_square <order>");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
    }

    let n: usize = args[1].parse().unwrap_or_else(|_| {
        usage();
        unreachable!()
    });

    if n < 1 {
        usage();
    }

    let model = LatinSquare::new();
    let options = Options::default();
    let solver = Solver::new(options);

    let formula = model.latin().and(model.qg5()).and(model.idempotent());
    let bounds = model.bounds(n)?;

    println!("Solving Latin square of order {}", n);

    let solution = solver.solve(&formula, &bounds)?;

    if let Some(instance) = solution.instance() {
        println!("{:?}", solution.statistics());

        if let Some(square_tuples) = instance.tuples(&model.square) {
            let tuples: Vec<_> = square_tuples.iter().collect();
            for i in 0..n {
                for j in 0..n {
                    let idx = i * n + j;
                    if idx < tuples.len() {
                        if let Some(atom) = tuples[idx].atom(2) {
                            if let Some(s) = atom_as_str(atom) {
                                print!("{}\t", s);
                            }
                        }
                    }
                }
                println!();
            }
        }
    } else {
        println!("{:?}", solution);
    }

    Ok(())
}
