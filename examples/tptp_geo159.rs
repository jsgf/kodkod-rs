//! GEO159 - Geometry model extending GEO158 with between relation
//!
//! The GEO159+1 problem from http://www.cs.miami.edu/~tptp/
//! Extends GEO158 with a "between" relation for points on curves.
//!
//! Following Java: kodkod.examples.tptp.GEO159

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::Bounds;
use kodkod_rs::solver::{Options, Solver};

#[allow(dead_code)]
mod tptp_geo158;
pub use tptp_geo158::GEO158;

pub struct GEO159 {
    pub base: GEO158,
    pub between: Relation,
}

impl GEO159 {
    pub fn new() -> Self {
        Self {
            base: GEO158::new(),
            between: Relation::nary("between_c", 4),
        }
    }

    /// Returns the between_c_defn axiom.
    /// all c, p, q, r: point |
    ///   c->p->q->r in between <=> p != r && some p.endPoint & r.endPoint & q.innerPoint & partOf.c
    pub fn between_defn(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let q = Variable::unary("Q");
        let r = Variable::unary("R");

        let e = Expression::from(p.clone()).join(Expression::from(self.base.end_point.clone()))
            .intersection(Expression::from(r.clone()).join(Expression::from(self.base.end_point.clone())))
            .intersection(Expression::from(q.clone()).join(Expression::from(self.base.inner_point.clone())))
            .intersection(Expression::from(self.base.part_of.clone()).join(Expression::from(c.clone())));

        let f0 = Expression::from(c.clone())
            .product(Expression::from(p.clone()))
            .product(Expression::from(q.clone()))
            .product(Expression::from(r.clone()))
            .in_set(Expression::from(self.between.clone()));
        let f1 = Expression::from(p.clone()).equals(Expression::from(q.clone())).not()
            .and(e.some());

        Formula::forall(
            Decls::from(Decl::one_of(p, Expression::from(self.base.point.clone())))
                .and(Decl::one_of(q, Expression::from(self.base.point.clone())))
                .and(Decl::one_of(r, Expression::from(self.base.point.clone())))
                .and(Decl::one_of(c, Expression::from(self.base.curve.clone()))),
            f0.iff(f1)
        )
    }

    /// Returns all the 'type' declarations.
    pub fn decls(&self) -> Formula {
        let curve_expr = Expression::from(self.base.curve.clone());
        let point_expr = Expression::from(self.base.point.clone());

        self.base.decls().and(
            Expression::from(self.between.clone())
                .in_set(curve_expr.product(point_expr.clone()).product(point_expr.clone()).product(point_expr))
        )
    }

    /// Returns the conjunction of all axioms and decls
    pub fn check_defs(&self) -> Formula {
        self.base.axioms().and(self.between_defn()).and(self.base.some_curve())
    }

    /// Returns bounds with the given scope for curves and points
    pub fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut b = self.base.bounds(scope)?;
        let f = b.universe().factory();

        let c = f.range(f.tuple(&["c0"])?, f.tuple(&[&format!("c{}", scope - 1)])?)?;
        let p = f.range(f.tuple(&["p0"])?, f.tuple(&[&format!("p{}", scope - 1)])?)?;

        // between: C x P x P x P
        b.bound(&self.between, f.none(4), c.product(&p)?.product(&p)?.product(&p)?)?;

        Ok(b)
    }
}

impl Default for GEO159 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_geo159 <scope>");
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

    let model = GEO159::new();
    let formula = model.check_defs();
    let bounds = model.bounds(n)?;

    println!("=== GEO159 (scope={n}) ===\n");

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
fn test_geo159_runs() {
    let model = GEO159::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_defs();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
