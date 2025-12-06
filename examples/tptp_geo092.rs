//! GEO092 - Geometry theorem extending GEO158
//!
//! The GEO092+1 problem from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.GEO092

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Variable};
use kodkod_rs::solver::{Options, Solver};

#[path = "tptp_geo158.rs"]
mod tptp_geo158;
pub use tptp_geo158::GEO158;

pub struct GEO092 {
    pub base: GEO158,
}

impl GEO092 {
    pub fn new() -> Self {
        Self {
            base: GEO158::new(),
        }
    }

    /// Returns the conjecture proposition_2_14_1.
    /// all c1, c2: curve, p: point |
    ///   p->c1->c2 in meet && c1->c2 in sum.open =>
    ///   all q: point - p | c1 + c2 !in q.incident
    pub fn proposition2141(&self) -> Formula {
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");
        let p = Variable::unary("P");
        let q = Variable::unary("Q");

        let e0 = Expression::from(c1.clone()).product(Expression::from(c2.clone()));

        let f0 = Expression::from(p.clone()).product(e0.clone())
            .in_set(Expression::from(self.base.meet.clone()))
            .and(e0.in_set(
                Expression::from(self.base.sum.clone()).join(Expression::from(self.base.open.clone()))
            ));

        let f1 = Expression::from(c1.clone())
            .union(Expression::from(c2.clone()))
            .in_set(Expression::from(q.clone()).join(Expression::from(self.base.incident.clone())))
            .not();

        let inner_forall = Formula::forall(
            Decls::from(Decl::one_of(q, Expression::from(self.base.point.clone()).difference(Expression::from(p.clone())))),
            f1
        );

        Formula::forall(
            Decls::from(Decl::one_of(c1, Expression::from(self.base.curve.clone())))
                .and(Decl::one_of(c2, Expression::from(self.base.curve.clone())))
                .and(Decl::one_of(p, Expression::from(self.base.point.clone()))),
            f0.implies(inner_forall)
        )
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    /// axioms() && !proposition2141()
    pub fn check_proposition2141(&self) -> Formula {
        self.base.axioms().and(self.proposition2141().not())
    }
}

impl Default for GEO092 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_geo092 <scope>");
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

    let model = GEO092::new();
    let formula = model.check_proposition2141();
    let bounds = model.base.bounds(n)?;

    println!("=== GEO092 (scope={n}) ===\n");

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
fn test_geo092_runs() {
    let model = GEO092::new();
    let bounds = model.base.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_proposition2141();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
