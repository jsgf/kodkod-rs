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

//! A Kodkod "unary" encoding of the Transpose4x4 synthesis problem with
//! holes on the left hand side.
//!
//! Based on kodkod.examples.xpose.Transpose4x4UnaryL

use kodkod_rs::ast::{Expression, Formula, IntExpression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Creates Expression for integer constant i
fn int_expr(i: i32) -> Expression {
    IntExpression::constant(i).to_expression()
}

/// Transpose4x4UnaryL synthesis problem
struct Transpose4x4UnaryL {
    mx1: [Relation; 4],
    mx2: [Relation; 4],
    sx1: [Relation; 4],
    sx2: [Relation; 4],
    mi: [[Relation; 4]; 4],
    si: [[Relation; 4]; 4],
    succ: Relation,
}

impl Transpose4x4UnaryL {
    fn new() -> Self {
        let mx1 = std::array::from_fn(|i| Relation::unary(&format!("mx1[{i}]")));
        let mx2 = std::array::from_fn(|i| Relation::unary(&format!("mx2[{i}]")));
        let sx1 = std::array::from_fn(|i| Relation::unary(&format!("sx1[{i}]")));
        let sx2 = std::array::from_fn(|i| Relation::unary(&format!("sx2[{i}]")));
        let mi: [[Relation; 4]; 4] =
            std::array::from_fn(|i| std::array::from_fn(|j| Relation::unary(&format!("mi[{i}, {j}]"))));
        let si: [[Relation; 4]; 4] =
            std::array::from_fn(|i| std::array::from_fn(|j| Relation::unary(&format!("si[{i}, {j}]"))));

        Self {
            mx1,
            mx2,
            sx1,
            sx2,
            mi,
            si,
            succ: Relation::binary("succ"),
        }
    }

    /// Representation invariants which ensure that every relation
    /// representing a hole is a singleton.
    fn invariants(&self) -> Formula {
        let mut inv = Vec::with_capacity(32);
        for i in 0..4 {
            inv.push(Expression::from(self.mx1[i].clone()).one());
            inv.push(Expression::from(self.mx2[i].clone()).one());
            inv.push(Expression::from(self.sx1[i].clone()).one());
            inv.push(Expression::from(self.sx2[i].clone()).one());
            for j in 0..4 {
                inv.push(Expression::from(self.mi[i][j].clone()).one());
                inv.push(Expression::from(self.si[i][j].clone()).one());
            }
        }
        Formula::and_all(inv)
    }

    /// Encodes seq[idx] using relational join
    fn get(&self, seq: Expression, idx: Expression) -> Expression {
        idx.join(seq)
    }

    /// Returns idx + k using successor relation
    fn add(&self, idx: Expression, k: usize) -> Expression {
        let mut ret = idx;
        for _ in 0..k {
            ret = self.get(Expression::from(self.succ.clone()), ret);
        }
        ret
    }

    /// Encodes the shufps SIMD instruction.
    /// Returns 0->xmm1[imm8[0]] + 1->xmm1[imm8[1]] + 2->xmm2[imm8[2]] + 3->xmm2[imm8[3]]
    fn shufps(&self, xmm1: Expression, xmm2: Expression, imm8: &[Relation; 4]) -> Expression {
        Expression::union_all(vec![
            int_expr(0).product(self.get(xmm1.clone(), Expression::from(imm8[0].clone()))),
            int_expr(1).product(self.get(xmm1, Expression::from(imm8[1].clone()))),
            int_expr(2).product(self.get(xmm2.clone(), Expression::from(imm8[2].clone()))),
            int_expr(3).product(self.get(xmm2, Expression::from(imm8[3].clone()))),
        ])
    }

    /// Encodes reading a subarray of length 4 from array m at position pos.
    /// Returns 0->m[pos] + 1->m[pos+1] + 2->m[pos+2] + 3->m[pos+3]
    fn rd4(&self, m: Expression, pos: Expression) -> Expression {
        Expression::union_all(vec![
            int_expr(0).product(self.get(m.clone(), pos.clone())),
            int_expr(1).product(self.get(m.clone(), self.add(pos.clone(), 1))),
            int_expr(2).product(self.get(m.clone(), self.add(pos.clone(), 2))),
            int_expr(3).product(self.get(m, self.add(pos, 3))),
        ])
    }

    /// Encodes writing 4 elements from src into dst at position pos.
    /// Returns dst ++ (pos->src[0] + (pos+1)->src[1] + (pos+2)->src[2] + (pos+3)->src[3])
    fn wr4(&self, dst: Expression, src: Expression, pos: i32) -> Expression {
        dst.override_with(Expression::union_all(vec![
            int_expr(pos).product(self.get(src.clone(), int_expr(0))),
            int_expr(pos + 1).product(self.get(src.clone(), int_expr(1))),
            int_expr(pos + 2).product(self.get(src.clone(), int_expr(2))),
            int_expr(pos + 3).product(self.get(src, int_expr(3))),
        ]))
    }

    /// Returns an expression that represents the transpose of m using shufps.
    fn transpose_shufps(&self, m: Expression) -> Expression {
        let s = Expression::univ().product(int_expr(0)); // s = new int[16];
        let t = Expression::univ().product(int_expr(0)); // t = new int[16];

        let s0 = self.wr4(
            s.clone(),
            self.shufps(
                self.rd4(m.clone(), Expression::from(self.mx1[0].clone())),
                self.rd4(m.clone(), Expression::from(self.mx2[0].clone())),
                &self.mi[0],
            ),
            0,
        );
        let s1 = self.wr4(
            s0,
            self.shufps(
                self.rd4(m.clone(), Expression::from(self.mx1[1].clone())),
                self.rd4(m.clone(), Expression::from(self.mx2[1].clone())),
                &self.mi[1],
            ),
            4,
        );
        let s2 = self.wr4(
            s1,
            self.shufps(
                self.rd4(m.clone(), Expression::from(self.mx1[2].clone())),
                self.rd4(m.clone(), Expression::from(self.mx2[2].clone())),
                &self.mi[2],
            ),
            8,
        );
        let s3 = self.wr4(
            s2,
            self.shufps(
                self.rd4(m.clone(), Expression::from(self.mx1[3].clone())),
                self.rd4(m, Expression::from(self.mx2[3].clone())),
                &self.mi[3],
            ),
            12,
        );

        let t0 = self.wr4(
            t.clone(),
            self.shufps(
                self.rd4(s3.clone(), Expression::from(self.sx1[0].clone())),
                self.rd4(s3.clone(), Expression::from(self.sx2[0].clone())),
                &self.si[0],
            ),
            0,
        );
        let t1 = self.wr4(
            t0,
            self.shufps(
                self.rd4(s3.clone(), Expression::from(self.sx1[1].clone())),
                self.rd4(s3.clone(), Expression::from(self.sx2[1].clone())),
                &self.si[1],
            ),
            4,
        );
        let t2 = self.wr4(
            t1,
            self.shufps(
                self.rd4(s3.clone(), Expression::from(self.sx1[2].clone())),
                self.rd4(s3.clone(), Expression::from(self.sx2[2].clone())),
                &self.si[2],
            ),
            8,
        );
        let t3 = self.wr4(
            t2,
            self.shufps(
                self.rd4(s3.clone(), Expression::from(self.sx1[3].clone())),
                self.rd4(s3, Expression::from(self.sx2[3].clone())),
                &self.si[3],
            ),
            12,
        );

        t3
    }

    /// Returns relation bounds over a universe of integers 0-15.
    fn bounds(&self) -> Bounds {
        let atoms: Vec<String> = (0..16).map(|i| i.to_string()).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs).unwrap();
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // s3: { 0, 1, 2, 3 }
        let s3 = factory.tuple_set(&[&["0"], &["1"], &["2"], &["3"]]).unwrap();
        // s12: { 0, ..., 12 }
        let s12 = factory
            .tuple_set(&[
                &["0"], &["1"], &["2"], &["3"], &["4"], &["5"], &["6"], &["7"], &["8"], &["9"],
                &["10"], &["11"], &["12"],
            ])
            .unwrap();

        for i in 0..4 {
            bounds.bound(&self.mx1[i], factory.none(1), s12.clone()).unwrap();
            bounds.bound(&self.mx2[i], factory.none(1), s12.clone()).unwrap();
            bounds.bound(&self.sx1[i], factory.none(1), s12.clone()).unwrap();
            bounds.bound(&self.sx2[i], factory.none(1), s12.clone()).unwrap();
            for j in 0..4 {
                bounds.bound(&self.mi[i][j], factory.none(1), s3.clone()).unwrap();
                bounds.bound(&self.si[i][j], factory.none(1), s3.clone()).unwrap();
            }
        }

        // ord: { [0, 1], [1, 2], ..., [14, 15] }
        let mut ord_tuples = Vec::new();
        for i in 0..15 {
            ord_tuples.push(vec![format!("{i}"), format!("{}", i + 1)]);
        }
        let ord_refs: Vec<Vec<&str>> = ord_tuples
            .iter()
            .map(|v| v.iter().map(|s| s.as_str()).collect())
            .collect();
        let ord_slices: Vec<&[&str]> = ord_refs.iter().map(|v| v.as_slice()).collect();
        let ord = factory.tuple_set(&ord_slices).unwrap();
        bounds.bound_exactly(&self.succ, ord).unwrap();

        bounds
    }

    /// Converts an integer array to a binary relation expression.
    /// Returns 0->val[0] + 1->val[1] + ... + (val.length-1)->val[val.length-1]
    fn to_expr(val: &[i32]) -> Expression {
        let exprs: Vec<Expression> = val
            .iter()
            .enumerate()
            .map(|(i, &v)| int_expr(i as i32).product(int_expr(v)))
            .collect();
        Expression::union_all(exprs)
    }

    /// Solves the synthesis problem for the given input matrix.
    fn solve(&self, m: &[i32; 16]) -> kodkod_rs::Result<kodkod_rs::solver::Solution> {
        let expected = transpose(m);
        let formula = self
            .invariants()
            .and(Self::to_expr(&expected).equals(self.transpose_shufps(Self::to_expr(m))));

        let mut options = Options::default();
        options.bool_options.bitwidth = 5;

        let solver = Solver::new(options);
        solver.solve(&formula, &self.bounds())
    }
}

/// Transposes a 4x4 matrix.
fn transpose(m: &[i32; 16]) -> [i32; 16] {
    let mut t = [0; 16];
    for i in 0..4 {
        for j in 0..4 {
            t[4 * i + j] = m[4 * j + i];
        }
    }
    t
}

fn run() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Transpose4x4 Synthesis (UnaryL) ===\n");

    let a: [i32; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

    let enc = Transpose4x4UnaryL::new();
    let solution = enc.solve(&a)?;

    println!("Result: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
    let stats = solution.statistics();
    println!(
        "  Variables: {}, Clauses: {}",
        stats.num_variables(),
        stats.num_clauses()
    );
    println!(
        "  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(),
        stats.solving_time(),
        stats.total_time()
    );

    if solution.is_sat() {
        println!("\nSynthesis successful!");
        println!("(Values can be extracted from the solution instance)");
    }

    Ok(())
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    run()
}

#[test]
fn test_xpose_transpose4x4_unary_l_runs() {
    run().unwrap();
}
