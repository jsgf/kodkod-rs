//! LAT258 - Lattice theory with distributivity conjecture
//!
//! A KK encoding of LAT258+1.p from http://www.cs.miami.edu/~tptp/
//! Models lattice operations (meet, join) with ordering and distributivity axioms.
//!
//! Following Java: kodkod.examples.tptp.LAT258

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct LAT258 {
    goal: Relation,
    p: Relation,
    t: Relation,
    u: Relation,
    v: Relation,
    w: Relation,
    x: Relation,
    y: Relation,
    z: Relation,
    less_than: Relation,
    meet: Relation,
    join: Relation,
}

impl LAT258 {
    fn new() -> Self {
        Self {
            goal: Relation::unary("goal"),
            p: Relation::unary("p"),
            t: Relation::unary("t"),
            u: Relation::unary("u"),
            v: Relation::unary("v"),
            w: Relation::unary("w"),
            x: Relation::unary("x"),
            y: Relation::unary("y"),
            z: Relation::unary("z"),
            less_than: Relation::binary("lessThan"),
            meet: Relation::ternary("meet"),
            join: Relation::ternary("join"),
        }
    }

    /// Returns function declarations.
    fn decls(&self) -> Formula {
        Expression::from(self.p.clone()).one()
            .and(Expression::from(self.t.clone()).one())
            .and(Expression::from(self.v.clone()).one())
            .and(Expression::from(self.w.clone()).one())
            .and(Expression::from(self.u.clone()).one())
            .and(Expression::from(self.x.clone()).one())
            .and(Expression::from(self.y.clone()).one())
            .and(Expression::from(self.z.clone()).one())
    }

    /// Returns the join_assumption axiom.
    /// x->y->t + x->z->u in join
    fn join_assumption(&self) -> Formula {
        Expression::from(self.x.clone())
            .product(Expression::from(self.y.clone()))
            .product(Expression::from(self.t.clone()))
            .union(Expression::from(self.x.clone())
                .product(Expression::from(self.z.clone()))
                .product(Expression::from(self.u.clone())))
            .in_set(Expression::from(self.join.clone()))
    }

    /// Returns the meet_assumption axiom.
    /// t->u->v in meet
    fn meet_assumption(&self) -> Formula {
        Expression::from(self.t.clone())
            .product(Expression::from(self.u.clone()))
            .product(Expression::from(self.v.clone()))
            .in_set(Expression::from(self.meet.clone()))
    }

    /// Returns the meet_join_assumption axiom.
    /// y->z->w in meet && x->w->p in join
    fn meet_join_assumption(&self) -> Formula {
        Expression::from(self.y.clone())
            .product(Expression::from(self.z.clone()))
            .product(Expression::from(self.w.clone()))
            .in_set(Expression::from(self.meet.clone()))
            .and(Expression::from(self.x.clone())
                .product(Expression::from(self.w.clone()))
                .product(Expression::from(self.p.clone()))
                .in_set(Expression::from(self.join.clone())))
    }

    /// Returns the goal_ax axiom.
    /// v->p in lessThan => some goal
    fn goal_ax(&self) -> Formula {
        Expression::from(self.v.clone())
            .product(Expression::from(self.p.clone()))
            .in_set(Expression::from(self.less_than.clone()))
            .implies(Expression::from(self.goal.clone()).some())
    }

    /// Returns the less_than_reflexive axiom.
    /// iden in lessThan
    fn less_than_reflexive(&self) -> Formula {
        Expression::IDEN.in_set(Expression::from(self.less_than.clone()))
    }

    /// Returns the less_than_transitive axiom.
    /// lessThan.lessThan in lessThan
    fn less_than_transitive(&self) -> Formula {
        Expression::from(self.less_than.clone())
            .join(Expression::from(self.less_than.clone()))
            .in_set(Expression::from(self.less_than.clone()))
    }

    /// Returns the lower_bound_meet axiom.
    /// all c: univ | meet.c in c.lessThan->c.lessThan
    fn lower_bound_meet(&self) -> Formula {
        let c = Variable::unary("C");
        let e0 = Expression::from(c.clone()).join(Expression::from(self.less_than.clone()));
        let f0 = Expression::from(self.meet.clone())
            .join(Expression::from(c.clone()))
            .in_set(e0.clone().product(e0));
        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::UNIV)),
            f0
        )
    }

    /// Returns the greatest_lower_bound_meet axiom.
    fn greatest_lower_bound_meet(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let e0 = Expression::from(b.clone())
            .join(Expression::from(a.clone()).join(Expression::from(self.meet.clone())));
        let f0 = e0.clone().some().implies(
            Expression::from(self.less_than.clone()).join(Expression::from(a.clone()))
                .intersection(Expression::from(self.less_than.clone()).join(Expression::from(b.clone())))
                .in_set(Expression::from(self.less_than.clone()).join(e0))
        );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f0
        )
    }

    /// Returns the upper_bound_join axiom.
    /// all c: univ | join.c in lessThan.c->lessThan.c
    fn upper_bound_join(&self) -> Formula {
        let c = Variable::unary("C");
        let e0 = Expression::from(self.less_than.clone()).join(Expression::from(c.clone()));
        let f0 = Expression::from(self.join.clone())
            .join(Expression::from(c.clone()))
            .in_set(e0.clone().product(e0));
        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::UNIV)),
            f0
        )
    }

    /// Returns the least_upper_bound_join axiom.
    fn least_upper_bound_join(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let e0 = Expression::from(b.clone())
            .join(Expression::from(a.clone()).join(Expression::from(self.meet.clone())));
        let f0 = e0.clone().some().implies(
            Expression::from(a.clone()).join(Expression::from(self.less_than.clone()))
                .intersection(Expression::from(b.clone()).join(Expression::from(self.less_than.clone())))
                .in_set(e0.join(Expression::from(self.less_than.clone())))
        );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f0
        )
    }

    /// Returns the less_than_meet_join axiom.
    /// all a: univ, b: a.lessThan | a->b->a in meet && a->b->b in join
    fn less_than_meet_join(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let e0 = Expression::from(a.clone()).product(Expression::from(b.clone()));
        let f0 = e0.clone().product(Expression::from(a.clone()))
            .in_set(Expression::from(self.meet.clone()));
        let f1 = e0.product(Expression::from(b.clone()))
            .in_set(Expression::from(self.join.clone()));
        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::UNIV)),
            Formula::forall(
                Decls::from(Decl::one_of(b, Expression::from(a).join(Expression::from(self.less_than.clone())))),
                f0.and(f1)
            )
        )
    }

    /// Helper for commutativity: e.univ~ in e.univ
    fn commutative(&self, e: Expression) -> Formula {
        let first2 = e.join(Expression::UNIV);
        first2.clone().transpose().in_set(first2)
    }

    /// Returns the commutativity_meet axiom.
    fn commutativity_meet(&self) -> Formula {
        self.commutative(Expression::from(self.meet.clone()))
    }

    /// Returns the commutativity_join axiom.
    fn commutativity_join(&self) -> Formula {
        self.commutative(Expression::from(self.join.clone()))
    }

    /// Helper for associativity: all a, b, c: univ | a->(c.(b.r))->(c.((b.(a.r)).r)) in r
    fn associative(&self, r: Expression) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let d = Expression::from(b.clone()).join(Expression::from(a.clone()).join(r.clone()));
        let e = Expression::from(c.clone()).join(d.join(r.clone()));
        let f = Expression::from(c.clone()).join(Expression::from(b.clone()).join(r.clone()));
        let f0 = Expression::from(a.clone()).product(f).product(e).in_set(r);
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV)),
            f0
        )
    }

    /// Returns the associativity_meet axiom.
    fn associativity_meet(&self) -> Formula {
        self.associative(Expression::from(self.meet.clone()))
    }

    /// Returns the associativity_join axiom.
    fn associativity_join(&self) -> Formula {
        self.associative(Expression::from(self.join.clone()))
    }

    /// Returns the lo_le_distr axiom (lower-to-lesser distributivity).
    fn lo_le_distr(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let h = Expression::from(c.clone())
            .join(Expression::from(b.clone()).join(Expression::from(self.join.clone())));
        let d = h.join(Expression::from(a.clone()).join(Expression::from(self.meet.clone())));
        let e = Expression::from(b.clone())
            .join(Expression::from(a.clone()).join(Expression::from(self.meet.clone())));
        let f = Expression::from(c.clone())
            .join(Expression::from(a.clone()).join(Expression::from(self.meet.clone())));
        let g = f.join(e.join(Expression::from(self.join.clone())));
        let f0 = d.product(g).in_set(Expression::from(self.less_than.clone()));
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV)),
            f0
        )
    }

    /// Returns the do_lattice axiom.
    /// UNIV × UNIV in meet.UNIV
    fn do_lattice(&self) -> Formula {
        Expression::UNIV.product(Expression::UNIV)
            .in_set(Expression::from(self.meet.clone()).join(Expression::UNIV))
    }

    /// Returns the goal_to_be_proved conjecture.
    fn goal_to_be_proved(&self) -> Formula {
        Expression::from(self.goal.clone()).some()
    }

    /// Returns the conjunction of all decls and axioms.
    fn axioms(&self) -> Formula {
        self.decls()
            .and(self.join_assumption())
            .and(self.meet_assumption())
            .and(self.meet_join_assumption())
            .and(self.goal_ax())
            .and(self.less_than_reflexive())
            .and(self.less_than_transitive())
            .and(self.lower_bound_meet())
            .and(self.greatest_lower_bound_meet())
            .and(self.upper_bound_join())
            .and(self.least_upper_bound_join())
            .and(self.less_than_meet_join())
            .and(self.commutativity_meet())
            .and(self.commutativity_join())
            .and(self.associativity_meet())
            .and(self.associativity_join())
            .and(self.lo_le_distr())
            .and(self.do_lattice())
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    fn check_goal_to_be_proved(&self) -> Formula {
        self.axioms().and(self.goal_to_be_proved().not())
    }

    /// Returns the bounds for the given scope.
    fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| format!("n{i}")).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();

        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        // goal can only be n0
        let n0 = f.tuple_set(&[&["n0"]])?;
        b.bound(&self.goal, f.none(1), n0)?;

        let all1 = f.all(1);
        b.bound(&self.p, f.none(1), all1.clone())?;
        b.bound(&self.t, f.none(1), all1.clone())?;
        b.bound(&self.v, f.none(1), all1.clone())?;
        b.bound(&self.w, f.none(1), all1.clone())?;
        b.bound(&self.u, f.none(1), all1.clone())?;
        b.bound(&self.x, f.none(1), all1.clone())?;
        b.bound(&self.y, f.none(1), all1.clone())?;
        b.bound(&self.z, f.none(1), all1)?;

        b.bound(&self.less_than, f.none(2), f.all(2))?;

        let all3 = f.all(3);
        b.bound(&self.join, f.none(3), all3.clone())?;
        b.bound(&self.meet, f.none(3), all3)?;

        Ok(b)
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_lat258 <scope>");
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

    let model = LAT258::new();
    let formula = model.check_goal_to_be_proved();
    let bounds = model.bounds(n)?;

    println!("=== LAT258 (n={n}) ===\n");

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    // UNSAT means the goal is proved (no counterexample)
    println!("{}", if solution.is_sat() { "SAT (counterexample found)" } else { "UNSAT (goal proved)" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}

#[test]
fn test_lat258_runs() {
    let model = LAT258::new();
    let formula = model.check_goal_to_be_proved();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    // Just verify it doesn't crash
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
