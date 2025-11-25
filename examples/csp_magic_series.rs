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

//! A Kodkod encoding of the magic series problem.
//!
//! Following Java: kodkod.examples.csp.MagicSeries

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::engine::Evaluator;
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solution, Solver};

struct MagicSeries {
    num: Relation,
    bits: Relation,
    el: Relation,
}

impl MagicSeries {
    fn new() -> Self {
        MagicSeries {
            num: Relation::unary("num"),
            bits: Relation::binary("bits"),
            el: Relation::binary("el"),
        }
    }

    /// Returns the magic series formula.
    fn magic(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let num_expr: Expression = self.num.clone().into();
        let el_expr: Expression = self.el.clone().into();
        let bits_expr: Expression = self.bits.clone().into();

        // final Expression e = y.join(el).eq(x.join(bits)).comprehension(y.oneOf(num));
        let y_expr: Expression = y.clone().into();
        let x_expr: Expression = x.clone().into();

        let e = y_expr.clone()
            .join(el_expr.clone())
            .equals(x_expr.clone().join(bits_expr))
            .comprehension(Decls::from(Decl::one_of(y.clone(), num_expr.clone())));

        // final Formula f1 = x.join(el).sum().eq(e.count()).forAll(x.oneOf(num));
        Formula::forall(
            Decls::from(Decl::one_of(x, num_expr)),
            x_expr.join(el_expr).sum_cast().eq(e.count())
        )
    }

    /// Bounds for a series with the given maximum.
    fn bounds(&self, max: i32) -> Bounds {
        assert!(max >= 1, "max must be 1 or greater: {max}");

        let mut atoms: Vec<String> = Vec::new();
        for i in 0..=max {
            atoms.push(i.to_string());
        }

        let u = Universe::new(&atoms.iter().map(|s| s.as_str()).collect::<Vec<_>>())
            .expect("Failed to create universe");
        let mut b = Bounds::new(u);
        let f = b.universe().factory();

        b.bound_exactly(&self.num, f.all(1)).unwrap();

        let num_bits = 32 - (max as u32).leading_zeros();
        let mut bit_atoms = f.none(1);
        for i in 0..num_bits {
            let bit_val = 1 << i;
            bit_atoms.add(f.tuple(&[&bit_val.to_string()]).unwrap()).unwrap();
            // Note: Java binds integer constants as relations, but Rust doesn't support this yet
            // b.boundExactly(bit_val, f.setOf(bit_val));
        }

        b.bound(&self.el, f.none(2), f.all(1).product(&bit_atoms).unwrap())
            .unwrap();

        let mut num2bits = f.none(2);
        for i in 0..=max {
            for j in 0..num_bits {
                let bit = 1 << j;
                if (i & bit) != 0 {
                    num2bits
                        .add(f.tuple(&[&i.to_string(), &bit.to_string()]).unwrap())
                        .unwrap();
                }
            }
        }
        b.bound_exactly(&self.bits, num2bits).unwrap();

        b
    }

    fn print(&self, sol: &Solution) {
        use kodkod_rs::instance::atom_as_str;

        match sol {
            Solution::Sat { instance, .. } => {
                println!("SATISFIABLE");
                println!("{:?}", sol.statistics());

                // Print the solution for el relation
                if let Some(el_tuples) = instance.tuples(&self.el) {
                    println!("Solution (showing el relation):");
                    for tuple in el_tuples.iter() {
                        if let (Some(num_atom), Some(bit_atom)) = (tuple.atom(0), tuple.atom(1)) {
                            let num_str = atom_as_str(num_atom).unwrap();
                            let bit_str = atom_as_str(bit_atom).unwrap();
                            println!("  {num_str} -> {bit_str}");
                        }
                    }
                }
            }
            Solution::Unsat { .. } => {
                println!("UNSATISFIABLE");
                println!("{:?}", sol.statistics());
            }
            Solution::Trivial { is_true, .. } => {
                if *is_true {
                    println!("TRIVIALLY TRUE");
                } else {
                    println!("TRIVIALLY FALSE");
                }
                println!("{:?}", sol.statistics());
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let max = if args.len() > 1 {
        args[1].parse::<i32>().unwrap_or(10)
    } else {
        10 // Default to 10 for quick testing
    };

    if max < 1 {
        eprintln!("Usage: {} <maximum number in the series>", args[0]);
        std::process::exit(1);
    }

    let model = MagicSeries::new();
    let f = model.magic();
    let b = model.bounds(max);

    let mut options = Options::default();
    let bitwidth = 33 - (max as u32).leading_zeros();
    options.bool_options.bitwidth = bitwidth as usize;

    let solver = Solver::new(options.clone());
    let sol = solver.solve(&f, &b).expect("Failed to solve");

    model.print(&sol);
}
