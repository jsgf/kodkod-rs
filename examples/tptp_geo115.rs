//! GEO115 - Geometry theorem extending GEO159
//!
//! KK encoding of GEO115+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.GEO115

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Variable};
use kodkod_rs::solver::{Options, Solver};

#[path = "tptp_geo159.rs"]
#[allow(dead_code)]
mod tptp_geo159;
pub use tptp_geo159::GEO159;

pub struct GEO115 {
    pub base: GEO159,
}

impl GEO115 {
    pub fn new() -> Self {
        Self {
            base: GEO159::new(),
        }
    }

    /// Returns the conjecture theorem_3_8_5.
    /// all c: curve, p, q, r: point |
    ///   c->p->q->r in between =>
    ///     incident.c - q in q.(p.(c.between)) + ((c.between).r).q
    pub fn theorem385(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let q = Variable::unary("Q");
        let r = Variable::unary("R");

        let f0 = Expression::from(c.clone())
            .product(Expression::from(p.clone()))
            .product(Expression::from(q.clone()))
            .product(Expression::from(r.clone()))
            .in_set(Expression::from(self.base.between.clone()));

        // q.(p.(c.between))
        let e0 = Expression::from(q.clone()).join(
            Expression::from(p.clone()).join(
                Expression::from(c.clone()).join(Expression::from(self.base.between.clone()))
            )
        );

        // ((c.between).r).q
        let e1 = Expression::from(c.clone())
            .join(Expression::from(self.base.between.clone()))
            .join(Expression::from(r.clone()))
            .join(Expression::from(q.clone()));

        // incident.c - q in e0 + e1
        let f1 = Expression::from(self.base.base.incident.clone())
            .join(Expression::from(c.clone()))
            .difference(Expression::from(q.clone()))
            .in_set(e0.union(e1));

        Formula::forall(
            Decls::from(Decl::one_of(p, Expression::from(self.base.base.point.clone())))
                .and(Decl::one_of(q, Expression::from(self.base.base.point.clone())))
                .and(Decl::one_of(r, Expression::from(self.base.base.point.clone())))
                .and(Decl::one_of(c, Expression::from(self.base.base.curve.clone()))),
            f0.implies(f1)
        )
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    /// axioms() && !theorem385()
    pub fn check_theorem385(&self) -> Formula {
        self.base.base.axioms().and(self.theorem385().not())
    }
}

impl Default for GEO115 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_geo115 <scope>");
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

    let model = GEO115::new();
    let formula = model.check_theorem385();
    let bounds = model.base.bounds(n)?;

    println!("=== GEO115 (scope={n}) ===\n");

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
fn test_geo115_runs() {
    let model = GEO115::new();
    let bounds = model.base.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_theorem385();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
