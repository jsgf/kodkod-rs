//! Viktor - Kuncak hypothesis for n=3
//!
//! A KK encoding of the Kuncak hypothesis for n = 3.
//!
//! Following Java: kodkod.examples.alloy.Viktor

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, IntExpression, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct Viktor {
    rows: usize,
    cols: usize,
    a: Vec<Vec<Relation>>,
    x: Vec<Relation>,
    b: Vec<IntExpression>,
}

impl Viktor {
    /// Constructs an instance of Viktor for n = 3
    fn new() -> Self {
        let rows = 3;
        let cols = 1 << rows; // 2^3 = 8

        // Create a[i][j] relations
        let mut a = Vec::new();
        for i in 0..rows {
            let mut row = Vec::new();
            for j in 0..cols {
                row.push(Relation::unary(&format!("a{}{}", i, j)));
            }
            a.push(row);
        }

        // Create x[j] relations
        let mut x = Vec::new();
        for j in 0..cols {
            x.push(Relation::unary(&format!("x{}", j)));
        }

        // Compute b[i] = conditionalSum(a[i], x, 0, cols-1)
        let mut b = Vec::new();
        for i in 0..rows {
            let a_row: Vec<Expression> = a[i].iter().map(|r| Expression::from(r.clone())).collect();
            let x_exprs: Vec<Expression> = x.iter().map(|r| Expression::from(r.clone())).collect();
            b.push(Self::conditional_sum(&a_row, &x_exprs, 0, cols - 1));
        }

        Self { rows, cols, a, x, b }
    }

    /// Returns the sum of the elements in x (conditional on the non-emptiness of a[i])
    /// located at indices [lo..hi]
    fn conditional_sum(a: &[Expression], x: &[Expression], lo: usize, hi: usize) -> IntExpression {
        if lo > hi {
            IntExpression::constant(0)
        } else if lo == hi {
            // a[lo].some() ? x[lo].sum() : 0
            a[lo].clone().some().then_else_int(
                x[lo].clone().sum_int(),
                IntExpression::constant(0)
            )
        } else {
            let mid = (lo + hi) / 2;
            let lsum = Self::conditional_sum(a, x, lo, mid);
            let hsum = Self::conditional_sum(a, x, mid + 1, hi);
            lsum.plus(hsum)
        }
    }

    /// Returns a formula constraining all x's to be singletons
    fn decls(&self) -> Formula {
        let mut ret = Formula::constant(true);
        for xj in &self.x {
            ret = ret.and(Expression::from(xj.clone()).one());
        }
        ret
    }

    /// Returns the equations to be satisfied
    fn equations(&self) -> Formula {
        // each b[i] <= cols-1
        let mut f0 = Formula::constant(true);
        let col_const = IntExpression::constant((self.cols - 1) as i32);
        for bi in &self.b {
            f0 = f0.and(bi.clone().lte(col_const.clone()));
        }

        // Create y variables for quantification over INTS
        let mut y = Vec::new();
        for i in 0..self.rows {
            y.push(Variable::unary(&format!("y{}", i)));
        }

        // Build declarations: y[0] in INTS && y[1] in INTS && y[2] in INTS
        let mut decls = Decls::from(Decl::one_of(y[0].clone(), Expression::INTS));
        for i in 1..self.rows {
            decls = decls.and(Decl::one_of(y[i].clone(), Expression::INTS));
        }

        // For all triples (i,j,k) where i<j<k,
        // assert that there do NOT exist y values satisfying the equations
        let mut f1 = Formula::constant(true);
        let mut combo = vec![Expression::NONE; self.rows];

        for i in 0..self.cols {
            for j in (i+1)..self.cols {
                for k in (j+1)..self.cols {
                    let mut f2 = Formula::constant(true);

                    for m in 0..self.rows {
                        combo[0] = Expression::from(self.a[m][i].clone());
                        combo[1] = Expression::from(self.a[m][j].clone());
                        combo[2] = Expression::from(self.a[m][k].clone());

                        let y_exprs: Vec<Expression> = y.iter()
                            .map(|v| Expression::from(v.clone()))
                            .collect();

                        let cond_sum = Self::conditional_sum(&combo, &y_exprs, 0, self.rows - 1);
                        f2 = f2.and(cond_sum.eq(self.b[m].clone()));
                    }

                    f1 = f1.and(Formula::forall(decls.clone(), f2.not()));
                }
            }
        }

        f0.and(f1)
    }

    /// Returns decls() && equations()
    fn check_equations(&self) -> Formula {
        self.decls().and(self.equations())
    }

    /// Returns the bounds for the problem
    fn bounds(&self) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms = Vec::new();
        for i in 0..self.cols {
            atoms.push(i.to_string());
        }
        atoms.push("a".to_string());

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // Bound all a[i][j] to {"a"}
        let abound = factory.set_of_atom("a")?;
        for i in 0..self.rows {
            for j in 0..self.cols {
                bounds.bound(&self.a[i][j], factory.none(1), abound.clone())?;
            }
        }

        // Bound all x[j] to {0..cols-1}
        let xbound = factory.range(
            factory.tuple(&["0"])?,
            factory.tuple(&[&(self.cols - 1).to_string()])?
        )?;
        for j in 0..self.cols {
            bounds.bound(&self.x[j], factory.none(1), xbound.clone())?;
            // Integer bounds: j -> {j}
            bounds.bound_exactly_int(j as i32, factory.set_of_atom(&j.to_string())?)?;
        }

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Viktor - Kuncak Hypothesis (n=3) ===\n");

    let model = Viktor::new();
    let formula = model.check_equations();
    let bounds = model.bounds()?;

    let mut options = Options::default();
    options.bool_options.bitwidth = 7;

    println!("Solving...");
    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds)?;

    println!("\nResult: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}
