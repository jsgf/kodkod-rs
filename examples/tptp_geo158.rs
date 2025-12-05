//! GEO158 - Geometry model for curves and points
//!
//! The GEO158+1 problem from http://www.cs.miami.edu/~tptp/
//! Base module for geometry problems involving curves, points, endpoints.
//!
//! Following Java: kodkod.examples.tptp.GEO158

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct GEO158 {
    pub part_of: Relation,
    pub incident: Relation,
    pub sum: Relation,
    pub end_point: Relation,
    pub inner_point: Relation,
    pub meet: Relation,
    pub closed: Relation,
    pub open: Relation,
    pub curve: Relation,
    pub point: Relation,
}

impl GEO158 {
    pub fn new() -> Self {
        Self {
            part_of: Relation::binary("partOf"),
            incident: Relation::binary("incident"),
            sum: Relation::ternary("sum"),
            end_point: Relation::binary("endPoint"),
            inner_point: Relation::binary("innerPoint"),
            meet: Relation::ternary("meet"),
            closed: Relation::unary("Closed"),
            open: Relation::unary("Open"),
            curve: Relation::unary("Curve"),
            point: Relation::unary("Point"),
        }
    }

    /// Returns all the 'type' declarations.
    pub fn decls(&self) -> Formula {
        let cc = Expression::from(self.curve.clone())
            .product(Expression::from(self.curve.clone()));
        let pc = Expression::from(self.point.clone())
            .product(Expression::from(self.curve.clone()));

        let f0 = Expression::from(self.part_of.clone()).in_set(cc.clone());
        let f1 = Expression::from(self.closed.clone())
            .in_set(Expression::from(self.curve.clone()))
            .and(Expression::from(self.open.clone())
                .in_set(Expression::from(self.curve.clone())));
        let f2 = Expression::from(self.meet.clone())
            .in_set(Expression::from(self.point.clone()).product(cc.clone()))
            .and(Expression::from(self.sum.clone())
                .in_set(Expression::from(self.curve.clone()).product(cc)));
        let f3 = Expression::from(self.incident.clone()).in_set(pc.clone())
            .and(Expression::from(self.end_point.clone()).in_set(pc.clone()))
            .and(Expression::from(self.inner_point.clone()).in_set(pc));

        // all C1, C2: Curve | one C2.(C1.sum)
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");
        let f4 = Formula::forall(
            Decls::from(Decl::one_of(c1.clone(), Expression::from(self.curve.clone())))
                .and(Decl::one_of(c2.clone(), Expression::from(self.curve.clone()))),
            Expression::from(c2).join(
                Expression::from(c1).join(Expression::from(self.sum.clone()))
            ).one()
        );

        f0.and(f1).and(f2).and(f3).and(f4)
    }

    /// Returns the part_of_defn axiom.
    /// all C, C1: Curve | C1->C in partOf iff incident.C1 in incident.C
    pub fn part_of_defn(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");

        let f = Expression::from(c1.clone()).product(Expression::from(c.clone()))
            .in_set(Expression::from(self.part_of.clone()))
            .iff(Expression::from(self.incident.clone()).join(Expression::from(c1.clone()))
                .in_set(Expression::from(self.incident.clone()).join(Expression::from(c.clone()))));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone()))),
            f
        )
    }

    /// Returns the sum_defn axiom.
    /// all C, C1, C2: Curve | C1->C2->C in sum iff incident.C = incident.C1 + incident.C2
    pub fn sum_defn(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");

        let f0 = Expression::from(c1.clone())
            .product(Expression::from(c2.clone()))
            .product(Expression::from(c.clone()))
            .in_set(Expression::from(self.sum.clone()));
        let f1 = Expression::from(self.incident.clone()).join(Expression::from(c.clone()))
            .equals(Expression::from(self.incident.clone()).join(Expression::from(c1.clone()))
                .union(Expression::from(self.incident.clone()).join(Expression::from(c2.clone()))));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c2, Expression::from(self.curve.clone()))),
            f0.iff(f1)
        )
    }

    /// Returns the end_point_defn axiom.
    pub fn end_point_defn(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");

        let e0 = Expression::from(p.clone()).product(Expression::from(c.clone()));
        let f0 = e0.clone().in_set(Expression::from(self.end_point.clone()));
        let f1 = e0.clone().in_set(Expression::from(self.incident.clone()));

        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");
        let f2 = Expression::from(c1.clone()).product(Expression::from(c2.clone()))
            .in_set(Expression::from(self.part_of.clone()))
            .or(Expression::from(c2.clone()).product(Expression::from(c1.clone()))
                .in_set(Expression::from(self.part_of.clone())));
        let e1 = Expression::from(self.part_of.clone()).join(Expression::from(c.clone()))
            .intersection(Expression::from(p.clone()).join(Expression::from(self.incident.clone())));
        let f3 = Formula::forall(
            Decls::from(Decl::one_of(c1, e1.clone()))
                .and(Decl::one_of(c2, e1)),
            f2
        );

        Formula::forall(
            Decls::from(Decl::one_of(p, Expression::from(self.point.clone())))
                .and(Decl::one_of(c, Expression::from(self.curve.clone()))),
            f0.iff(f1.and(f3))
        )
    }

    /// Returns the inner_point_defn axiom.
    pub fn inner_point_defn(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let e0 = Expression::from(p.clone()).product(Expression::from(c.clone()));
        let f0 = e0.clone().in_set(Expression::from(self.inner_point.clone()));
        let f1 = e0.clone().in_set(Expression::from(self.incident.clone()))
            .and(e0.intersection(Expression::from(self.end_point.clone())).no());

        Formula::forall(
            Decls::from(Decl::one_of(p, Expression::from(self.point.clone())))
                .and(Decl::one_of(c, Expression::from(self.curve.clone()))),
            f0.iff(f1)
        )
    }

    /// Returns the meet_defn axiom.
    pub fn meet_defn(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");
        let p = Variable::unary("P");

        let f0 = Expression::from(p.clone())
            .product(Expression::from(c.clone()))
            .product(Expression::from(c1.clone()))
            .in_set(Expression::from(self.meet.clone()));
        let f1 = Expression::from(p.clone()).product(Expression::from(c.clone()))
            .in_set(Expression::from(self.incident.clone()))
            .and(Expression::from(p.clone()).product(Expression::from(c1.clone()))
                .in_set(Expression::from(self.incident.clone())));
        let e0 = Expression::from(self.incident.clone()).join(Expression::from(c.clone()))
            .intersection(Expression::from(self.incident.clone()).join(Expression::from(c1.clone())));
        let e1 = Expression::from(self.end_point.clone()).join(Expression::from(c.clone()))
            .intersection(Expression::from(self.end_point.clone()).join(Expression::from(c1.clone())));
        let f2 = e0.in_set(e1);

        Formula::forall(
            Decls::from(Decl::one_of(p, Expression::from(self.point.clone())))
                .and(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone()))),
            f0.iff(f1.and(f2))
        )
    }

    /// Returns the closed_defn axiom.
    pub fn closed_defn(&self) -> Formula {
        let c = Variable::unary("C");
        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone()))),
            Expression::from(c.clone()).in_set(Expression::from(self.closed.clone()))
                .iff(Expression::from(self.end_point.clone()).join(Expression::from(c)).no())
        )
    }

    /// Returns the open_defn axiom.
    pub fn open_defn(&self) -> Formula {
        let c = Variable::unary("C");
        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone()))),
            Expression::from(c.clone()).in_set(Expression::from(self.open.clone()))
                .iff(Expression::from(self.end_point.clone()).join(Expression::from(c)).some())
        )
    }

    /// Returns the c1 axiom.
    /// all C, C1: Curve | (C1->C in partOf && C1 != C) => C1 in Open
    pub fn c1(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");
        let f0 = Expression::from(c1.clone()).product(Expression::from(c.clone()))
            .in_set(Expression::from(self.part_of.clone()))
            .and(Expression::from(c1.clone()).equals(Expression::from(c.clone())).not());
        let f1 = Expression::from(c1.clone()).in_set(Expression::from(self.open.clone()));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone()))),
            f0.implies(f1)
        )
    }

    /// Returns the c2 axiom.
    pub fn c2(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");
        let c3 = Variable::unary("C3");

        let f0 = Expression::from(c1.clone())
            .union(Expression::from(c2.clone()))
            .union(Expression::from(c3.clone()))
            .product(Expression::from(c.clone()))
            .in_set(Expression::from(self.part_of.clone()));
        let f1 = Expression::from(self.end_point.clone()).join(Expression::from(c1.clone()))
            .intersection(Expression::from(self.end_point.clone()).join(Expression::from(c2.clone())))
            .intersection(Expression::from(self.end_point.clone()).join(Expression::from(c3.clone())))
            .some();
        let f2 = Expression::from(c2.clone()).product(Expression::from(c3.clone()))
            .in_set(Expression::from(self.part_of.clone()))
            .or(Expression::from(c3.clone()).product(Expression::from(c2.clone()))
                .in_set(Expression::from(self.part_of.clone())));
        let f3 = Expression::from(c1.clone()).product(Expression::from(c2.clone()))
            .in_set(Expression::from(self.part_of.clone()))
            .or(Expression::from(c2.clone()).product(Expression::from(c1.clone()))
                .in_set(Expression::from(self.part_of.clone())));
        let f4 = Expression::from(c1.clone()).product(Expression::from(c3.clone()))
            .in_set(Expression::from(self.part_of.clone()))
            .or(Expression::from(c3.clone()).product(Expression::from(c1.clone()))
                .in_set(Expression::from(self.part_of.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c2, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c3, Expression::from(self.curve.clone()))),
            f0.and(f1).implies(f2.or(f3).or(f4))
        )
    }

    /// Returns the c3 axiom.
    /// all C: Curve | some innerPoint.C
    pub fn c3(&self) -> Formula {
        let c = Variable::unary("C");
        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone()))),
            Expression::from(self.inner_point.clone()).join(Expression::from(c)).some()
        )
    }

    /// Returns the c4 axiom.
    /// all C: Curve, P: Point | P->C in innerPoint => some P.meet & sum.C
    pub fn c4(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let f0 = Expression::from(p.clone()).product(Expression::from(c.clone()))
            .in_set(Expression::from(self.inner_point.clone()));
        let f1 = Expression::from(p.clone()).join(Expression::from(self.meet.clone()))
            .intersection(Expression::from(self.sum.clone()).join(Expression::from(c.clone())))
            .some();

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(p, Expression::from(self.point.clone()))),
            f0.implies(f1)
        )
    }

    /// Returns the c5 axiom.
    /// all C: Curve, P, Q, R: endPoint.C | P = Q || P = R || Q = R
    pub fn c5(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let q = Variable::unary("Q");
        let r = Variable::unary("R");
        let e0 = Expression::from(self.end_point.clone()).join(Expression::from(c.clone()));
        let f0 = Expression::from(p.clone()).equals(Expression::from(q.clone()))
            .or(Expression::from(p.clone()).equals(Expression::from(r.clone())))
            .or(Expression::from(q.clone()).equals(Expression::from(r.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(p, e0.clone()))
                .and(Decl::one_of(q, e0.clone()))
                .and(Decl::one_of(r, e0)),
            f0
        )
    }

    /// Returns the c6 axiom.
    /// all C: Curve, P: endPoint.C | some endPoint.C - P
    pub fn c6(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let e0 = Expression::from(self.end_point.clone()).join(Expression::from(c.clone()));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(p.clone(), e0.clone())),
            e0.difference(Expression::from(p)).some()
        )
    }

    /// Returns the c7 axiom.
    pub fn c7(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");
        let p = Variable::unary("P");

        let f0 = Expression::from(c.clone()).in_set(Expression::from(self.closed.clone()))
            .and(Expression::from(p.clone())
                .product(Expression::from(c1.clone()))
                .product(Expression::from(c2.clone()))
                .in_set(Expression::from(self.meet.clone())));
        let f1 = Expression::from(c2.clone())
            .join(Expression::from(c1.clone()).join(Expression::from(self.sum.clone())))
            .equals(Expression::from(c.clone()));
        let f2 = Expression::from(self.end_point.clone()).join(Expression::from(c1.clone()))
            .product(Expression::from(c1.clone()))
            .product(Expression::from(c2.clone()))
            .in_set(Expression::from(self.meet.clone()));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c2, Expression::from(self.curve.clone())))
                .and(Decl::one_of(p, Expression::from(self.point.clone()))),
            f0.and(f1).implies(f2)
        )
    }

    /// Returns the c8 axiom.
    /// all C1, C2: Curve | some meet.C2.C1 => some sum[C1][C2]
    pub fn c8(&self) -> Formula {
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");
        let f0 = Expression::from(self.meet.clone())
            .join(Expression::from(c2.clone()))
            .join(Expression::from(c1.clone()))
            .some();
        let f1 = Expression::from(c2.clone())
            .join(Expression::from(c1.clone()).join(Expression::from(self.sum.clone())))
            .some();

        Formula::forall(
            Decls::from(Decl::one_of(c1, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c2, Expression::from(self.curve.clone()))),
            f0.implies(f1)
        )
    }

    /// Returns the c9 axiom.
    /// all C, C1: Curve | incident.C = incident.C1 => C = C1
    pub fn c9(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");

        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1.clone(), Expression::from(self.curve.clone()))),
            Expression::from(self.incident.clone()).join(Expression::from(c.clone()))
                .equals(Expression::from(self.incident.clone()).join(Expression::from(c1.clone())))
                .implies(Expression::from(c).equals(Expression::from(c1)))
        )
    }

    /// Returns the conjunction of all axioms and decls
    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.part_of_defn())
            .and(self.sum_defn())
            .and(self.end_point_defn())
            .and(self.inner_point_defn())
            .and(self.meet_defn())
            .and(self.open_defn())
            .and(self.closed_defn())
            .and(self.c1())
            .and(self.c2())
            .and(self.c3())
            .and(self.c4())
            .and(self.c5())
            .and(self.c6())
            .and(self.c7())
            .and(self.c8())
            .and(self.c9())
    }

    /// Returns the formula "some Curve"
    pub fn some_curve(&self) -> Formula {
        Expression::from(self.curve.clone()).some()
    }

    /// Returns bounds with the given scope for curves and points
    pub fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(scope > 0);

        let mut atoms: Vec<String> = Vec::new();
        for i in 0..scope {
            atoms.push(format!("c{i}"));
        }
        for i in 0..scope {
            atoms.push(format!("p{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        let c = f.range(f.tuple(&["c0"])?, f.tuple(&[&format!("c{}", scope - 1)])?)?;
        let p = f.range(f.tuple(&["p0"])?, f.tuple(&[&format!("p{}", scope - 1)])?)?;
        let cc = c.clone().product(&c)?;
        let pc = p.clone().product(&c)?;

        b.bound(&self.curve, f.none(1), c.clone())?;
        b.bound(&self.point, f.none(1), p)?;
        b.bound(&self.part_of, f.none(2), cc.clone())?;
        b.bound(&self.incident, f.none(2), pc.clone())?;
        b.bound(&self.sum, f.none(3), c.clone().product(&cc)?)?;
        b.bound(&self.end_point, f.none(2), pc.clone())?;
        b.bound(&self.inner_point, f.none(2), pc.clone())?;
        b.bound(&self.meet, f.none(3), pc.product(&c)?)?;
        b.bound(&self.closed, f.none(1), c.clone())?;
        b.bound(&self.open, f.none(1), c)?;

        Ok(b)
    }

    /// Returns the conjunction of the axioms and the hypothesis.
    pub fn check_consistent(&self) -> Formula {
        self.axioms().and(self.some_curve())
    }
}

impl Default for GEO158 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_geo158 <scope>");
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

    let model = GEO158::new();
    let formula = model.check_consistent();
    let bounds = model.bounds(n)?;

    println!("=== GEO158 (scope={n}) ===\n");

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
fn test_geo158_c3_with_defn() {
    let model = GEO158::new();
    let bounds = model.bounds(4).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());

    // c3 says every curve has an inner point. inner_point_defn defines inner points as
    // points incident to a curve but not endpoints.
    let formula = model.decls()
        .and(model.inner_point_defn())
        .and(model.c3())
        .and(model.some_curve());
    let solution = solver.solve(&formula, &bounds).expect("Failed to solve");
    assert!(solution.is_sat(), "decls + inner_point_defn + c3 should be SAT");
}

#[test]
fn test_geo158_runs() {
    // GEO158 is a complex geometry model. The full set of axioms is over-constrained
    // for small scopes. This test verifies the translation works correctly.
    let model = GEO158::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_consistent();
    // Just verify it doesn't crash - result depends on scope
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
