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

//! Various Kodkod encodings of the nqueens problem
//! (purely relational, an explicitly encoding that
//! uses integers, and a smarter integer encoding
//! that uses a logarithmic number of bits).
//!
//! Following Java: kodkod.examples.csp.NQueens

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, IntExpression, Relation, Variable};
use kodkod_rs::instance::{Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solution, Solver};

trait NQueens {
    /// Returns an encoding of the problem.
    fn rules(&self) -> Formula;

    /// Returns bounds for this encoding of the nqueens problem.
    fn bounds(&self) -> Bounds;

    /// Prints the given solution
    fn print(&self, instance: &Instance, options: &Options);
}

/// A relational encoding of nqueens.
struct RelQueens {
    queen: Relation,
    x: Relation,
    y: Relation,
    num: Relation,
    ord: Relation,
    n: usize,
}

impl RelQueens {
    fn new(n: usize) -> Self {
        assert!(n > 0);
        RelQueens {
            n,
            queen: Relation::unary("Queen"),
            x: Relation::binary("x"),
            y: Relation::binary("y"),
            num: Relation::unary("num"),
            ord: Relation::binary("ord"),
        }
    }
}

impl NQueens for RelQueens {
    /// Returns a relational encoding of the problem.
    fn rules(&self) -> Formula {
        let mut rules = Vec::new();

        let queen_expr: Expression = self.queen.clone().into();
        let num_expr: Expression = self.num.clone().into();
        let x_expr: Expression = self.x.clone().into();
        let y_expr: Expression = self.y.clone().into();

        rules.push(self.x.clone().function(queen_expr.clone(), num_expr.clone()));
        rules.push(self.y.clone().function(queen_expr.clone(), num_expr.clone()));

        let i = Variable::unary("n");
        // at most one queen in each row: all i: num | lone x.i
        let i_expr: Expression = i.clone().into();
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(i.clone(), num_expr.clone())),
            x_expr.clone().join(i_expr.clone()).lone()
        ));

        // at most one queen in each column: all i: num | lone y.i
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(i, num_expr.clone())),
            y_expr.clone().join(i_expr).lone()
        ));

        let q1 = Variable::unary("q1");
        let q2 = Variable::unary("q2");

        // at most one queen on each diagonal
        //         all q1: Queen, q2: Queen - q1 |
        //     let xu = prevs[q2.x] + prevs[q1.x],
        //          xi =  prevs[q2.x] & prevs[q1.x],
        //          yu = prevs[q2.y] + prevs[q1.y],
        //          yi = prevs[q2.y] & prevs[q1.y] |
        //     #(xu - xi) != #(yu - yi)
        let ord_closure = Expression::from(self.ord.clone()).closure();

        let q1_expr: Expression = q1.clone().into();
        let q2_expr: Expression = q2.clone().into();

        let q2x_prevs = ord_closure.clone().join(q2_expr.clone().join(x_expr.clone()));
        let q1x_prevs = ord_closure.clone().join(q1_expr.clone().join(x_expr.clone()));
        let q2y_prevs = ord_closure.clone().join(q2_expr.clone().join(y_expr.clone()));
        let q1y_prevs = ord_closure.join(q1_expr.clone().join(y_expr));

        let x_diff = q2x_prevs.clone().union(q1x_prevs.clone())
            .difference(q2x_prevs.intersection(q1x_prevs))
            .count();
        let y_diff = q2y_prevs.clone().union(q1y_prevs.clone())
            .difference(q2y_prevs.intersection(q1y_prevs))
            .count();

        rules.push(Formula::forall(
            Decls::from_vec(vec![
                Decl::one_of(q1, queen_expr.clone()),
                Decl::one_of(q2, queen_expr.difference(q1_expr)),
            ]),
            x_diff.eq(y_diff).not()
        ));

        Formula::and_all(rules)
    }

    /// Returns the bounds for relational encoding of the problem.
    fn bounds(&self) -> Bounds {
        let n = self.n;
        let mut atoms: Vec<String> = Vec::with_capacity(n * 2);

        for i in 0..n {
            atoms.push(format!("Q{i}"));
        }

        for i in 0..n {
            atoms.push(i.to_string());
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)
            .expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let f = b.universe().factory();

        let qbound = f.range(
            f.tuple(&["Q0"]).unwrap(),
            f.tuple(&[&format!("Q{}", n-1)]).unwrap()
        ).unwrap();
        let nbound = f.range(
            f.tuple(&["0"]).unwrap(),
            f.tuple(&[&(n-1).to_string()]).unwrap()
        ).unwrap();

        b.bound_exactly(&self.queen, qbound.clone()).unwrap();
        b.bound_exactly(&self.num, nbound.clone()).unwrap();
        b.bound(&self.x, f.none(2), qbound.clone().product(&nbound).unwrap()).unwrap();
        b.bound(&self.y, f.none(2), qbound.product(&nbound).unwrap()).unwrap();

        let mut obound = f.none(2);
        for i in 1..n {
            obound.add(f.tuple(&[&(i-1).to_string(), &i.to_string()]).unwrap()).unwrap();
        }

        b.bound_exactly(&self.ord, obound).unwrap();

        // Bind integer constants to their corresponding universe atoms
        for i in 0..n {
            b.bound_exactly_int(i as i32, f.set_of_atom(&i.to_string()).unwrap()).unwrap();
        }

        b
    }

    /// Prints the given solution
    fn print(&self, instance: &Instance, _options: &Options) {
        use kodkod_rs::instance::atom_as_str;

        // Build a map of queen positions from the solution
        let mut board = vec![vec![false; self.n]; self.n];

        if let Some(x_tuples) = instance.tuples(&self.x) {
            if let Some(y_tuples) = instance.tuples(&self.y) {
                // x contains (queen, col) pairs
                // y contains (queen, row) pairs
                // We need to match them up

                for x_tuple in x_tuples.iter() {
                    let queen_atom = x_tuple.atom(0).unwrap();
                    let col_atom = x_tuple.atom(1).unwrap();
                    let col_str = atom_as_str(col_atom).unwrap();
                    let col: usize = col_str.parse().unwrap();

                    // Find the corresponding row for this queen
                    for y_tuple in y_tuples.iter() {
                        let y_queen_atom = y_tuple.atom(0).unwrap();
                        if atom_as_str(queen_atom) == atom_as_str(y_queen_atom) {
                            let row_atom = y_tuple.atom(1).unwrap();
                            let row_str = atom_as_str(row_atom).unwrap();
                            let row: usize = row_str.parse().unwrap();
                            board[row][col] = true;
                            break;
                        }
                    }
                }
            }
        }

        // Print the board
        for row in &board {
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

/// A log encoding of nqueens
struct LogQueens {
    queen: Relation,
    x: Relation,
    y: Relation,
    n: usize,
}

impl LogQueens {
    /// Constructs an nqueens instance for the given n.
    fn new(n: usize) -> Self {
        assert!(n > 0);
        LogQueens {
            n,
            queen: Relation::unary("Queen"),
            x: Relation::binary("x"),
            y: Relation::binary("y"),
        }
    }
}

impl NQueens for LogQueens {
    /// Returns a log integer encoding of the problem.
    fn rules(&self) -> Formula {
        let mut rules = Vec::new();

        let queen_expr: Expression = self.queen.clone().into();
        let x_expr: Expression = self.x.clone().into();
        let y_expr: Expression = self.y.clone().into();

        let q1 = Variable::unary("q1");
        let q2 = Variable::unary("q2");

        // max row number is less than the number of queens
        // all q1: Queen | q1.x <= #queen-1
        let n_less_one = IntExpression::constant((self.n - 1) as i32);
        let q1_expr: Expression = q1.clone().into();
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(q1.clone(), queen_expr.clone())),
            q1_expr.clone().join(x_expr.clone()).sum_int().lte(n_less_one.clone())
        ));

        // max col number is less than the number of queens
        // all q1: Queen | q1.y <= #queen-1
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(q1.clone(), queen_expr.clone())),
            q1_expr.clone().join(y_expr.clone()).sum_int().lte(n_less_one)
        ));

        // at most one queen in each row:
        // all q1, q2: Queen | q1.x = q2.x => q1 = q2
        let q2_expr: Expression = q2.clone().into();
        rules.push(Formula::forall(
            Decls::from_vec(vec![
                Decl::one_of(q1.clone(), queen_expr.clone()),
                Decl::one_of(q2.clone(), queen_expr.clone()),
            ]),
            q1_expr.clone().join(x_expr.clone()).equals(q2_expr.clone().join(x_expr.clone()))
                .implies(q1_expr.clone().equals(q2_expr.clone()))
        ));

        // at most one queen in each column:
        // all q1, q2: Queen | q1.y = q2.y => q1 = q2
        rules.push(Formula::forall(
            Decls::from_vec(vec![
                Decl::one_of(q1.clone(), queen_expr.clone()),
                Decl::one_of(q2.clone(), queen_expr.clone()),
            ]),
            q1_expr.clone().join(y_expr.clone()).equals(q2_expr.clone().join(y_expr.clone()))
                .implies(q1_expr.clone().equals(q2_expr.clone()))
        ));

        // at most one queen on each diagonal :
        // all q1: Queen, q2: Queen - q1 | abs[q2.x - q1.x] != abs[q2.y - q1.y]

        let x_abs_diff = q2_expr.clone().join(x_expr.clone()).sum_int()
            .minus(q1_expr.clone().join(x_expr).sum_int())
            .abs();
        let y_abs_diff = q2_expr.clone().join(y_expr.clone()).sum_int()
            .minus(q1_expr.clone().join(y_expr).sum_int())
            .abs();

        rules.push(Formula::forall(
            Decls::from_vec(vec![
                Decl::one_of(q1.clone(), queen_expr.clone()),
                Decl::one_of(q2, queen_expr.difference(q1_expr)),
            ]),
            x_abs_diff.eq(y_abs_diff).not()
        ));

        Formula::and_all(rules)
    }

    /// Returns bounds for the log integer encoding.
    fn bounds(&self) -> Bounds {
        let n = self.n;
        let bits = 32 - (n as i32 - 1).leading_zeros() as usize;
        let mut atoms: Vec<String> = Vec::with_capacity(n + bits);

        for i in 0..n {
            atoms.push(format!("Q{i}"));
        }
        for i in 0..bits {
            atoms.push((1i32 << i).to_string());
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)
            .expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let f = b.universe().factory();

        let queens = f.range(
            f.tuple(&["Q0"]).unwrap(),
            f.tuple(&[&format!("Q{}", n-1)]).unwrap()
        ).unwrap();
        let ints = f.range(
            f.tuple(&["1"]).unwrap(),
            f.tuple(&[&(1i32 << (bits - 1)).to_string()]).unwrap()
        ).unwrap();

        b.bound_exactly(&self.queen, queens.clone()).unwrap();
        b.bound(&self.x, f.none(2), queens.clone().product(&ints).unwrap()).unwrap();
        b.bound(&self.y, f.none(2), queens.product(&ints).unwrap()).unwrap();

        // Bind integer constants (powers of 2) to their corresponding universe atoms
        for i in 0..bits {
            let val = 1i32 << i;
            b.bound_exactly_int(val, f.set_of_atom(&val.to_string()).unwrap()).unwrap();
        }

        b
    }

    /// Prints the given solution
    fn print(&self, instance: &Instance, _options: &Options) {
        use kodkod_rs::instance::atom_as_str;
        use std::collections::HashMap;

        // Build a map from queen to (x_sum, y_sum)
        let mut queen_positions: HashMap<String, (i32, i32)> = HashMap::new();

        if let Some(x_tuples) = instance.tuples(&self.x) {
            for x_tuple in x_tuples.iter() {
                let queen_atom = x_tuple.atom(0).unwrap();
                let col_bit_atom = x_tuple.atom(1).unwrap();
                let queen_str = atom_as_str(queen_atom).unwrap().to_string();
                let col_bit_str = atom_as_str(col_bit_atom).unwrap();
                let col_bit: i32 = col_bit_str.parse().unwrap();

                queen_positions.entry(queen_str.clone())
                    .or_insert((0, 0))
                    .0 += col_bit;
            }
        }

        if let Some(y_tuples) = instance.tuples(&self.y) {
            for y_tuple in y_tuples.iter() {
                let queen_atom = y_tuple.atom(0).unwrap();
                let row_bit_atom = y_tuple.atom(1).unwrap();
                let queen_str = atom_as_str(queen_atom).unwrap().to_string();
                let row_bit_str = atom_as_str(row_bit_atom).unwrap();
                let row_bit: i32 = row_bit_str.parse().unwrap();

                queen_positions.entry(queen_str.clone())
                    .or_insert((0, 0))
                    .1 += row_bit;
            }
        }

        // Build board
        let mut board = vec![vec![false; self.n]; self.n];
        for (_queen, (col_sum, row_sum)) in &queen_positions {
            if *col_sum >= 0 && *row_sum >= 0 {
                let col = *col_sum as usize;
                let row = *row_sum as usize;
                if row < self.n && col < self.n {
                    board[row][col] = true;
                }
            }
        }

        // Print the board
        for row in &board {
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

/// An explicit integer encoding of nqueens
struct IntQueens {
    queen: Relation,
    x: Relation,
    y: Relation,
    n: usize,
}

impl IntQueens {
    /// Constructs an nqueens instance for the given n.
    fn new(n: usize) -> Self {
        assert!(n > 0);
        IntQueens {
            n,
            queen: Relation::unary("Queen"),
            x: Relation::binary("x"),
            y: Relation::binary("y"),
        }
    }
}

impl NQueens for IntQueens {
    /// Returns an explicit integer encoding of the problem.
    fn rules(&self) -> Formula {
        let mut rules = Vec::new();

        let queen_expr: Expression = self.queen.clone().into();
        let x_expr: Expression = self.x.clone().into();
        let y_expr: Expression = self.y.clone().into();

        rules.push(self.x.clone().function(queen_expr.clone(), Expression::INTS));
        rules.push(self.y.clone().function(queen_expr.clone(), Expression::INTS));

        let i = Variable::unary("n");
        // at most one queen in each row: all i: INTS | lone x.i
        let i_expr: Expression = i.clone().into();
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(i.clone(), Expression::INTS)),
            x_expr.clone().join(i_expr.clone()).lone()
        ));

        // at most one queen in each column: all i: INTS | lone y.i
        rules.push(Formula::forall(
            Decls::from(Decl::one_of(i, Expression::INTS)),
            y_expr.clone().join(i_expr).lone()
        ));

        let q1 = Variable::unary("q1");
        let q2 = Variable::unary("q2");
        let q1_expr: Expression = q1.clone().into();
        let q2_expr: Expression = q2.clone().into();

        // at most one queen on each diagonal :
        // all q1: Queen, q2: Queen - q1 | abs[sum[q2.x] - sum[q1.x]] != abs[sum[q2.y] - sum[q1.y]]

        let x_abs_diff = q2_expr.clone().join(x_expr.clone()).sum_int()
            .minus(q1_expr.clone().join(x_expr).sum_int())
            .abs();
        let y_abs_diff = q2_expr.clone().join(y_expr.clone()).sum_int()
            .minus(q1_expr.clone().join(y_expr).sum_int())
            .abs();

        rules.push(Formula::forall(
            Decls::from_vec(vec![
                Decl::one_of(q1.clone(), queen_expr.clone()),
                Decl::one_of(q2, queen_expr.difference(q1_expr)),
            ]),
            x_abs_diff.eq(y_abs_diff).not()
        ));

        Formula::and_all(rules)
    }

    /// Returns bounds for the explicit integer encoding.
    fn bounds(&self) -> Bounds {
        let n = self.n;
        let atoms: Vec<String> = (0..n).map(|i| i.to_string()).collect();

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)
            .expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let f = b.universe().factory();

        b.bound_exactly(&self.queen, f.all(1)).unwrap();
        b.bound(&self.x, f.none(2), f.all(2)).unwrap();
        b.bound(&self.y, f.none(2), f.all(2)).unwrap();

        // Bind integer constants to their corresponding universe atoms
        for i in 0..n {
            b.bound_exactly_int(i as i32, f.set_of_atom(&i.to_string()).unwrap()).unwrap();
        }

        b
    }

    /// Prints the given solution
    fn print(&self, instance: &Instance, _options: &Options) {
        use kodkod_rs::instance::atom_as_str;

        // Debug: print what's in the instance
        println!("IntQueens solution:");
        if let Some(x_tuples) = instance.tuples(&self.x) {
            println!("x relation has {} tuples:", x_tuples.size());
            for tuple in x_tuples.iter() {
                print!("  ");
                for i in 0..tuple.arity() {
                    if let Some(atom) = tuple.atom(i) {
                        print!("{:?} ", atom);
                    }
                }
                println!();
            }
        }

        if let Some(y_tuples) = instance.tuples(&self.y) {
            println!("y relation has {} tuples:", y_tuples.size());
            for tuple in y_tuples.iter() {
                print!("  ");
                for i in 0..tuple.arity() {
                    if let Some(atom) = tuple.atom(i) {
                        print!("{:?} ", atom);
                    }
                }
                println!();
            }
        }

        // Build board from solution
        let mut board = vec![vec![false; self.n]; self.n];
        if let Some(x_tuples) = instance.tuples(&self.x) {
            if let Some(y_tuples) = instance.tuples(&self.y) {
                for x_tuple in x_tuples.iter() {
                    let queen_atom = x_tuple.atom(0).unwrap();
                    let col_atom = x_tuple.atom(1).unwrap();
                    let queen_str = atom_as_str(queen_atom).unwrap();
                    let col_str = atom_as_str(col_atom).unwrap();
                    let _queen_idx: usize = queen_str.parse().unwrap();
                    let col: usize = col_str.parse().unwrap();

                    // Find corresponding row
                    for y_tuple in y_tuples.iter() {
                        let y_queen_atom = y_tuple.atom(0).unwrap();
                        if atom_as_str(queen_atom) == atom_as_str(y_queen_atom) {
                            let row_atom = y_tuple.atom(1).unwrap();
                            let row_str = atom_as_str(row_atom).unwrap();
                            let row: usize = row_str.parse().unwrap();
                            board[row][col] = true;
                            break;
                        }
                    }
                }
            }
        }

        // Print the board
        for row in &board {
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

fn usage() {
    eprintln!("Usage: csp_nqueens <positive number of queens> <encoding: int | log | rel>");
    std::process::exit(1);
}

fn run() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 3 {
        usage();
    }

    let n = match args[1].parse::<usize>() {
        Ok(n) if n > 0 => n,
        _ => {
            usage();
            return;
        }
    };

    let encoding = args[2].to_lowercase();

    match encoding.as_str() {
        "int" => {
            let model = IntQueens::new(n);
            solve_and_print(&model, n);
        }
        "log" => {
            let model = LogQueens::new(n);
            solve_and_print(&model, n);
        }
        "rel" => {
            let model = RelQueens::new(n);
            solve_and_print(&model, n);
        }
        _ => usage(),
    }
}

fn main() {
    run()
}

fn solve_and_print<T: NQueens>(model: &T, n: usize) {
    let f = model.rules();
    let b = model.bounds();

    println!("encoding:");
    println!("{f:?}");

    let mut options = Options::default();
    // Set bitwidth based on n (matching Java implementation)
    options.bool_options.bitwidth = 33 - (n as i32 - 1).leading_zeros() as usize;

    let solver = Solver::new(options.clone());
    let sol = solver.solve(&f, &b).expect("Failed to solve");

    match &sol {
        Solution::Sat { instance, .. } => {
            println!("solution:");
            model.print(instance, &options);
        }
        _ => {
            println!("no solution");
        }
    }

    println!("{:?}", sol.statistics());
}


#[test]
fn test_csp_nqueens_small() {
    // Test with a small N-Queens problem (4-Queens)
    let n = 4;
    let queens = RelQueens::new(n);
    let formula = queens.rules();
    let bounds = queens.bounds();

    let mut options = Options::default();
    options.bool_options.bitwidth = 33 - (n as i32 - 1).leading_zeros() as usize;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds).expect("Solver should not error");

    // 4-Queens should be satisfiable
    assert!(solution.is_sat(), "4-Queens should have a solution");

    println!("N-Queens test passed - SAT as expected");
}
