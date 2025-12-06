//! MED009 - Medical domain conjecture
//!
//! A KK encoding of MED009+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.MED009

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Variable};
use kodkod_rs::solver::{Options, Solver};

#[path = "tptp_med001.rs"]
mod tptp_med001;
pub use tptp_med001::MED001;

pub struct MED009 {
    pub base: MED001,
}

impl MED009 {
    pub fn new() -> Self {
        Self {
            base: MED001::new(),
        }
    }

    /// Returns transsls2_qige27 conjecture.
    pub fn transsls2_qige27(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let n0 = Expression::from(self.base.n0.clone());
        let gt = Expression::from(self.base.gt.clone());
        let s1 = Expression::from(self.base.s1.clone());
        let s2 = Expression::from(self.base.s2.clone());
        let conditionhyper = Expression::from(self.base.conditionhyper.clone());
        let bcapacitysn = Expression::from(self.base.bcapacitysn.clone());
        let bcapacityne = Expression::from(self.base.bcapacityne.clone());
        let bcapacityex = Expression::from(self.base.bcapacityex.clone());
        let qilt27 = Expression::from(self.base.qilt27.clone());

        // The only difference from MED007: n0.in(qilt27).not() instead of n0.in(qilt27)
        let f0 = n0.clone().in_set(s1)
            .and(n0.clone().join(gt.clone()).in_set(conditionhyper.clone()))
            .and(n0.clone().in_set(bcapacitysn).not())
            .and(n0.clone().in_set(qilt27).not());

        let f1 = n0.product(Expression::from(x0.clone())).in_set(gt.clone()).not()
            .and(Expression::from(x0.clone()).in_set(s2))
            .and(Expression::from(x0.clone()).join(gt).in_set(conditionhyper))
            .and(Expression::from(x0.clone()).in_set(bcapacityne.union(bcapacityex)));

        let f1_exists = Formula::exists(
            Decls::from(Decl::one_of(x0, Expression::univ())),
            f1
        );

        f0.implies(f1_exists)
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    /// axioms() && !transsls2_qige27()
    pub fn check_transsls2_qige27(&self) -> Formula {
        self.base.axioms().and(self.transsls2_qige27().not())
    }
}

impl Default for MED009 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_med009 <scope>");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        usage();
    }

    let n: usize = args[1].parse().unwrap_or_else(|_| usage());
    if n < 1 {
        usage();
    }

    let model = MED009::new();
    let formula = model.check_transsls2_qige27();
    let bounds = model.base.bounds(n)?;

    println!("=== MED009 (scope={n}) ===\n");

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    println!("{}", if solution.is_sat() { "SAT" } else { "UNSAT" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}

#[test]
fn test_med009_runs() {
    let model = MED009::new();
    let bounds = model.base.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_transsls2_qige27();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
