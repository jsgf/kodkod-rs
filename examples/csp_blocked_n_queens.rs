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

//! Blocked N-Queens Problem
//!
//! Relational Kodkod encoding of the N-Queens problem with blocked positions.
//! Following Java: kodkod.examples.csp.BlockedNQueens

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{atom_as_str, Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solver};
use rand::Rng;

struct BlockedNQueens {
    queen: Relation,
    x: Relation,
    y: Relation,
    blocked: Relation,
    num: Relation,
    ord: Relation,
}

impl BlockedNQueens {
    fn new() -> Self {
        Self {
            queen: Relation::unary("Queen"),
            x: Relation::binary("x"),
            y: Relation::binary("y"),
            blocked: Relation::binary("blocked"),
            num: Relation::unary("num"),
            ord: Relation::binary("ord"),
        }
    }

    /// Returns a relational encoding of the problem
    fn rules(&self) -> Formula {
        let mut rules = Vec::new();

        // x and y are functions from queens to numbers
        rules.push(Formula::RelationPredicate(
            kodkod_rs::ast::RelationPredicate::Function {
                relation: self.x.clone(),
                domain: Expression::from(self.queen.clone()),
                range: Expression::from(self.num.clone()),
            }
        ));
        rules.push(Formula::RelationPredicate(
            kodkod_rs::ast::RelationPredicate::Function {
                relation: self.y.clone(),
                domain: Expression::from(self.queen.clone()),
                range: Expression::from(self.num.clone()),
            }
        ));

        let i = Variable::unary("n");
        let q1 = Variable::unary("q1");
        let q2 = Variable::unary("q2");

        // at most one queen in each row: all i: num | lone x.i
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(i.clone(), Expression::from(self.num.clone()))),
            Expression::from(self.x.clone()).join(Expression::from(i)).lone()
        ));

        // at most one queen in each column: all i: num | lone y.i
        let i2 = Variable::unary("n2");
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(i2.clone(), Expression::from(self.num.clone()))),
            Expression::from(self.y.clone()).join(Expression::from(i2)).lone()
        ));

        // no queen in a blocked position: all q: Queen | q.x->q.y !in blocked
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(q1.clone(), Expression::from(self.queen.clone()))),
            Expression::from(q1.clone())
                .join(Expression::from(self.x.clone()))
                .product(Expression::from(q1.clone()).join(Expression::from(self.y.clone())))
                .intersection(Expression::from(self.blocked.clone()))
                .no()
        ));

        // at most one queen on each diagonal
        let ord_closure = Expression::from(self.ord.clone()).closure();
        let q2x_prevs = ord_closure.clone().join(Expression::from(q2.clone()).join(Expression::from(self.x.clone())));
        let q1x_prevs = ord_closure.clone().join(Expression::from(q1.clone()).join(Expression::from(self.x.clone())));
        let q2y_prevs = ord_closure.clone().join(Expression::from(q2.clone()).join(Expression::from(self.y.clone())));
        let q1y_prevs = ord_closure.join(Expression::from(q1.clone()).join(Expression::from(self.y.clone())));

        let x_diff = q2x_prevs.clone()
            .union(q1x_prevs.clone())
            .difference(q2x_prevs.intersection(q1x_prevs))
            .count();
        let y_diff = q2y_prevs.clone()
            .union(q1y_prevs.clone())
            .difference(q2y_prevs.intersection(q1y_prevs))
            .count();

        rules.push(Formula::forall(
            Decls::from(Decl::one_of(q1.clone(), Expression::from(self.queen.clone())))
                .and(Decl::one_of(q2.clone(), Expression::from(self.queen.clone()).difference(Expression::from(q1)))),
            x_diff.eq(y_diff).not()
        ));

        Formula::and_all(rules)
    }

    /// Returns bounds for n queens with randomly blocked positions
    fn bounds(&self, n: usize, num_blocked: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::new();

        // Queens
        for i in 0..n {
            atoms.push(format!("Q{i}"));
        }

        // Numbers
        for i in 0..n {
            atoms.push(i.to_string());
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // Queen bounds
        let queen_tuples: Vec<Vec<&str>> = (0..n).map(|i| vec![&*atoms[i]]).collect();
        let queen_refs: Vec<&[&str]> = queen_tuples.iter().map(|v| v.as_slice()).collect();
        let qbound = factory.tuple_set(&queen_refs)?;

        // Number bounds
        let num_tuples: Vec<Vec<&str>> = (0..n).map(|i| vec![&*atoms[n + i]]).collect();
        let num_refs: Vec<&[&str]> = num_tuples.iter().map(|v| v.as_slice()).collect();
        let nbound = factory.tuple_set(&num_refs)?;

        bounds.bound_exactly(&self.queen, qbound.clone())?;
        bounds.bound_exactly(&self.num, nbound.clone())?;
        bounds.bound(&self.x, factory.none(2), qbound.product(&nbound)?)?;
        bounds.bound(&self.y, factory.none(2), qbound.product(&nbound)?)?;

        // Ordering relation
        let mut obound = factory.none(2);
        for i in 1..n {
            obound.add(factory.tuple(&[&*atoms[n + i - 1], &*atoms[n + i]])?)?;
        }
        bounds.bound_exactly(&self.ord, obound)?;

        // Bind integer constants
        for i in 0..n {
            bounds.bound_exactly_int(i as i32, factory.tuple_set(&[&[&*atoms[n + i]]])?)?;
        }

        // Generate random blocked positions
        let mut blocks = factory.none(2);
        let mut rng = rand::thread_rng();
        for _ in 0..num_blocked.min(n * n / 2) {
            let i = rng.gen_range(0..n);
            let j = rng.gen_range(0..n);
            blocks.add(factory.tuple(&[&*atoms[n + i], &*atoms[n + j]])?)?;
        }
        bounds.bound_exactly(&self.blocked, blocks)?;

        Ok(bounds)
    }

    /// Print the solution
    fn print(&self, instance: &Instance) {
        let n = instance.tuples(&self.queen).unwrap().size();

        // Build a map of (x, y) -> bool indicating if there's a queen
        let x_tuples = instance.tuples(&self.x).unwrap();
        let y_tuples = instance.tuples(&self.y).unwrap();

        let mut grid = vec![vec![false; n]; n];

        // For each queen, find its x and y coordinates
        for queen_idx in 0..n {
            let mut x_coord = None;
            let mut y_coord = None;

            // Find x coordinate for this queen
            for tuple in x_tuples.iter() {
                if let Some(atom) = tuple.atom(0) {
                    if let Some(name) = atom_as_str(atom) {
                        if name == format!("Q{queen_idx}") {
                            if let Some(coord_atom) = tuple.atom(1) {
                                if let Some(coord_str) = atom_as_str(coord_atom) {
                                    x_coord = coord_str.parse::<usize>().ok();
                                }
                            }
                            break;
                        }
                    }
                }
            }

            // Find y coordinate for this queen
            for tuple in y_tuples.iter() {
                if let Some(atom) = tuple.atom(0) {
                    if let Some(name) = atom_as_str(atom) {
                        if name == format!("Q{queen_idx}") {
                            if let Some(coord_atom) = tuple.atom(1) {
                                if let Some(coord_str) = atom_as_str(coord_atom) {
                                    y_coord = coord_str.parse::<usize>().ok();
                                }
                            }
                            break;
                        }
                    }
                }
            }

            if let (Some(x), Some(y)) = (x_coord, y_coord) {
                grid[y][x] = true;
            }
        }

        // Print the grid
        for row in &grid {
            for &has_queen in row {
                if has_queen {
                    print!(" Q");
                } else {
                    print!(" .");
                }
            }
            println!();
        }
    }
}

fn run() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    let n = if args.len() > 1 {
        args[1].parse().unwrap_or(8)
    } else {
        8
    };

    let num_blocked = if args.len() > 2 {
        args[2].parse().unwrap_or(5)
    } else {
        5
    };

    println!("=== Blocked {n}-Queens Problem (with {num_blocked} blocked positions) ===\n");

    let model = BlockedNQueens::new();
    let formula = model.rules();
    let bounds = model.bounds(n, num_blocked)?;

    let opts = Options::default();

    let solver = Solver::new(opts);
    let solution = solver.solve(&formula, &bounds)?;

    if solution.is_sat() {
        println!("Solution found:");
        model.print(solution.instance().unwrap());
    } else {
        println!("No solution found");
    }

    let stats = solution.statistics();
    println!("\nStatistics:");
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    run()
}

#[test]
fn test_csp_blocked_n_queens_runs() {
    // Test that the example runs without panicking
    run().unwrap();
}
