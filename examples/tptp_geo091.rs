//! GEO091 - Geometry model theorem 2_13
//!
//! The GEO091+1 problem from http://www.cs.miami.edu/~tptp/
//! Extends GEO158 with theorem_2_13 about curves and endpoints.
//!
//! Following Java: kodkod.examples.tptp.GEO091

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// GEO091 model - extends GEO158 with theorem_2_13
struct GEO091 {
    part_of: Relation,
    incident: Relation,
    sum: Relation,
    end_point: Relation,
    inner_point: Relation,
    meet: Relation,
    closed: Relation,
    open: Relation,
    curve: Relation,
    point: Relation,
}

impl GEO091 {
    fn new() -> Self {
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

    // All the GEO158 methods are inherited here (same as tptp_geo158.rs)

    fn decls(&self) -> Formula {
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

    fn part_of_defn(&self) -> Formula {
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

    fn sum_defn(&self) -> Formula {
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

    fn end_point_defn(&self) -> Formula {
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

    fn inner_point_defn(&self) -> Formula {
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

    fn meet_defn(&self) -> Formula {
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

    fn closed_defn(&self) -> Formula {
        let c = Variable::unary("C");
        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone()))),
            Expression::from(c.clone()).in_set(Expression::from(self.closed.clone()))
                .iff(Expression::from(self.end_point.clone()).join(Expression::from(c)).no())
        )
    }

    fn open_defn(&self) -> Formula {
        let c = Variable::unary("C");
        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone()))),
            Expression::from(c.clone()).in_set(Expression::from(self.open.clone()))
                .iff(Expression::from(self.end_point.clone()).join(Expression::from(c)).some())
        )
    }

    fn c1(&self) -> Formula {
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

    fn c2(&self) -> Formula {
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

    fn c3(&self) -> Formula {
        let c = Variable::unary("C");
        Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::from(self.curve.clone()))),
            Expression::from(self.inner_point.clone()).join(Expression::from(c)).some()
        )
    }

    fn c4(&self) -> Formula {
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

    fn c5(&self) -> Formula {
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

    fn c6(&self) -> Formula {
        let c = Variable::unary("C");
        let p = Variable::unary("P");
        let e0 = Expression::from(self.end_point.clone()).join(Expression::from(c.clone()));
        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(p.clone(), e0.clone())),
            e0.difference(Expression::from(p)).some()
        )
    }

    fn c7(&self) -> Formula {
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

    fn c8(&self) -> Formula {
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

    fn c9(&self) -> Formula {
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

    fn axioms(&self) -> Formula {
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

    /// Returns the conjecture theorem_2_13.
    /// all C, C1, C2: Curve |
    ///   ((C1 + C2)->C in partOf && C in Open &&
    ///   !(lone endPoint.C1 & endPoint.C2)) => C1 = C2
    fn theorem_2_13(&self) -> Formula {
        let c = Variable::unary("C");
        let c1 = Variable::unary("C1");
        let c2 = Variable::unary("C2");

        // (C1 + C2)->C in partOf
        let f0 = Expression::from(c1.clone())
            .union(Expression::from(c2.clone()))
            .product(Expression::from(c.clone()))
            .in_set(Expression::from(self.part_of.clone()));

        // C in Open
        let f0 = f0.and(Expression::from(c.clone())
            .in_set(Expression::from(self.open.clone())));

        // !(lone endPoint.C1 & endPoint.C2)
        let f1 = Expression::from(self.end_point.clone())
            .join(Expression::from(c1.clone()))
            .intersection(Expression::from(self.end_point.clone())
                .join(Expression::from(c2.clone())))
            .lone()
            .not();

        // C1 = C2
        let consequent = Expression::from(c1.clone()).equals(Expression::from(c2.clone()));

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c1, Expression::from(self.curve.clone())))
                .and(Decl::one_of(c2, Expression::from(self.curve.clone()))),
            f0.and(f1).implies(consequent)
        )
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    fn check_theorem_2_13(&self) -> Formula {
        self.axioms().and(self.theorem_2_13().not())
    }

    fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
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
}

fn usage() -> ! {
    eprintln!("Usage: tptp_geo091 <scope>");
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

    let model = GEO091::new();
    let formula = model.check_theorem_2_13();
    let bounds = model.bounds(n)?;

    println!("=== GEO091 (scope={n}) ===\n");

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    // UNSAT means the theorem holds (no counterexample found)
    println!("{}", if solution.is_sat() { "SAT (counterexample found)" } else { "UNSAT (theorem holds)" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}

#[test]
fn test_geo091_runs() {
    // GEO091 is a complex geometry theorem. This test verifies the translation works.
    let model = GEO091::new();
    let formula = model.check_theorem_2_13();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    // Just verify it doesn't crash
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
