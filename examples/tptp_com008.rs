//! COM008 - Computing theory confluence problem
//!
//! A KK encoding of COM008+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.COM008

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct COM008 {
    pub equalish: Relation,
    pub rewrite: Relation,
    pub trr: Relation,
    pub a: Relation,
    pub b: Relation,
    pub c: Relation,
    pub goal: Relation,
    pub atom: Relation,
}

impl COM008 {
    pub fn new() -> Self {
        Self {
            equalish: Relation::binary("equalish"),
            rewrite: Relation::binary("rewrite"),
            trr: Relation::binary("trr"),
            a: Relation::unary("a"),
            b: Relation::unary("b"),
            c: Relation::unary("c"),
            goal: Relation::unary("goal"),
            atom: Relation::unary("Atom"),
        }
    }

    /// Returns the declarations.
    /// one a && one b && one c
    pub fn decls(&self) -> Formula {
        Expression::from(self.a.clone()).one()
            .and(Expression::from(self.b.clone()).one())
            .and(Expression::from(self.c.clone()).one())
    }

    /// Returns the found axiom.
    /// all A: Atom | (b->A + c->A in trr) => some goal
    pub fn found(&self) -> Formula {
        let va = Variable::unary("A");
        let a_expr = Expression::from(va.clone());
        let b_expr = Expression::from(self.b.clone());
        let c_expr = Expression::from(self.c.clone());
        let trr = Expression::from(self.trr.clone());
        let goal = Expression::from(self.goal.clone());

        let f = b_expr.product(a_expr.clone())
            .union(c_expr.product(a_expr))
            .in_set(trr)
            .implies(goal.some());

        Formula::forall(
            Decls::from(Decl::one_of(va, Expression::from(self.atom.clone()))),
            f
        )
    }

    /// Returns the assumption axiom.
    /// a->b + a->c in trr
    pub fn assumption(&self) -> Formula {
        Expression::from(self.a.clone())
            .product(Expression::from(self.b.clone()))
            .union(Expression::from(self.a.clone()).product(Expression::from(self.c.clone())))
            .in_set(Expression::from(self.trr.clone()))
    }

    /// Returns the reflexivity axiom.
    /// (equalish.Atom) -> (equalish.Atom) & iden in equalish
    pub fn reflexivity(&self) -> Formula {
        let eqdom = Expression::from(self.equalish.clone())
            .join(Expression::from(self.atom.clone()));

        eqdom.clone()
            .product(eqdom)
            .intersection(Expression::iden())
            .in_set(Expression::from(self.equalish.clone()))
    }

    /// Returns the symmetry axiom.
    /// equalish = ~equalish
    pub fn symmetry(&self) -> Formula {
        Expression::from(self.equalish.clone())
            .equals(Expression::from(self.equalish.clone()).transpose())
    }

    /// Returns the equalish_in_transitive_reflexive_rewrite axiom.
    pub fn equalish_in_trr(&self) -> Formula {
        Expression::from(self.equalish.clone())
            .in_set(Expression::from(self.trr.clone()))
    }

    /// Returns the rewrite_in_transitive_reflexive_rewrite axiom.
    pub fn rewrite_in_trr(&self) -> Formula {
        Expression::from(self.rewrite.clone())
            .in_set(Expression::from(self.trr.clone()))
    }

    /// Returns the transitivity_of_transitive_reflexive_rewrite axiom.
    /// trr.trr in trr
    pub fn transitivity_of_trr(&self) -> Formula {
        Expression::from(self.trr.clone())
            .join(Expression::from(self.trr.clone()))
            .in_set(Expression::from(self.trr.clone()))
    }

    /// Returns the lo_cfl axiom.
    /// all A, B, C: Atom | (A->B + A->C in rewrite) => some (B.trr & C.trr)
    pub fn lo_cfl(&self) -> Formula {
        let va = Variable::unary("A");
        let vb = Variable::unary("B");
        let vc = Variable::unary("C");

        let f0 = Expression::from(va.clone())
            .product(Expression::from(vb.clone()))
            .union(Expression::from(va.clone()).product(Expression::from(vc.clone())))
            .in_set(Expression::from(self.rewrite.clone()));

        let f1 = Expression::from(vb.clone())
            .join(Expression::from(self.trr.clone()))
            .intersection(Expression::from(vc.clone()).join(Expression::from(self.trr.clone())))
            .some();

        Formula::forall(
            Decls::from(Decl::one_of(va, Expression::from(self.atom.clone())))
                .and(Decl::one_of(vb, Expression::from(self.atom.clone())))
                .and(Decl::one_of(vc, Expression::from(self.atom.clone()))),
            f0.implies(f1)
        )
    }

    /// Returns the ih_cfl axiom.
    /// all A, B, C: Atom | (a->A in rewrite && A->B + A->C in trr) => some (B.trr & C.trr)
    pub fn ih_cfl(&self) -> Formula {
        let va = Variable::unary("A");
        let vb = Variable::unary("B");
        let vc = Variable::unary("C");

        let f0 = Expression::from(self.a.clone())
            .product(Expression::from(va.clone()))
            .in_set(Expression::from(self.rewrite.clone()))
            .and(
                Expression::from(va.clone())
                    .product(Expression::from(vb.clone()))
                    .union(Expression::from(va.clone()).product(Expression::from(vc.clone())))
                    .in_set(Expression::from(self.trr.clone()))
            );

        let f1 = Expression::from(vb.clone())
            .join(Expression::from(self.trr.clone()))
            .intersection(Expression::from(vc.clone()).join(Expression::from(self.trr.clone())))
            .some();

        Formula::forall(
            Decls::from(Decl::one_of(va, Expression::from(self.atom.clone())))
                .and(Decl::one_of(vb, Expression::from(self.atom.clone())))
                .and(Decl::one_of(vc, Expression::from(self.atom.clone()))),
            f0.implies(f1)
        )
    }

    /// Returns the equalish_or_rewrite axiom.
    /// all A, B: Atom | A->B in trr => (A->B in equalish || some (A.rewrite & trr.B))
    pub fn equalish_or_rewrite(&self) -> Formula {
        let va = Variable::unary("A");
        let vb = Variable::unary("B");

        let f0 = Expression::from(va.clone())
            .product(Expression::from(vb.clone()))
            .in_set(Expression::from(self.trr.clone()));

        let f1 = Expression::from(va.clone())
            .product(Expression::from(vb.clone()))
            .in_set(Expression::from(self.equalish.clone()));

        let f2 = Expression::from(va.clone())
            .join(Expression::from(self.rewrite.clone()))
            .intersection(Expression::from(self.trr.clone()).join(Expression::from(vb.clone())))
            .some();

        Formula::forall(
            Decls::from(Decl::one_of(va, Expression::from(self.atom.clone())))
                .and(Decl::one_of(vb, Expression::from(self.atom.clone()))),
            f0.implies(f1.or(f2))
        )
    }

    /// Returns the conjunction of all axioms.
    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.equalish_in_trr())
            .and(self.rewrite_in_trr())
            .and(self.found())
            .and(self.assumption())
            .and(self.reflexivity())
            .and(self.symmetry())
            .and(self.transitivity_of_trr())
            .and(self.lo_cfl())
            .and(self.ih_cfl())
            .and(self.equalish_or_rewrite())
    }

    /// Returns the conjecture.
    /// some goal
    pub fn goal_to_be_proved(&self) -> Formula {
        Expression::from(self.goal.clone()).some()
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    /// axioms() && !goalToBeProved()
    pub fn check_goal_to_be_proved(&self) -> Formula {
        self.axioms().and(self.goal_to_be_proved().not())
    }

    /// Returns bounds for the given scope.
    pub fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let mut atoms: Vec<String> = Vec::with_capacity(n + 1);
        atoms.push("goal".to_string());
        for i in 0..n {
            atoms.push(format!("a{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        let d1 = f.range(f.tuple(&["a0"])?, f.tuple(&[&format!("a{}", n - 1)])?)?;
        let d2 = d1.clone().product(&d1)?;

        b.bound(&self.rewrite, f.none(2), d2.clone())?;
        b.bound(&self.equalish, f.none(2), d2.clone())?;
        b.bound(&self.a, f.none(1), d1.clone())?;
        b.bound(&self.b, f.none(1), d1.clone())?;
        b.bound(&self.c, f.none(1), d1.clone())?;
        b.bound_exactly(&self.atom, d1)?;
        b.bound(&self.trr, f.none(2), d2)?;
        b.bound(&self.goal, f.none(1), f.set_of_atom("goal")?)?;

        Ok(b)
    }
}

impl Default for COM008 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_com008 <scope>");
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

    let model = COM008::new();
    let formula = model.check_goal_to_be_proved();
    let bounds = model.bounds(n)?;

    println!("=== COM008 (scope={n}) ===\n");

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
fn test_com008_runs() {
    let model = COM008::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_goal_to_be_proved();
    let solution = solver.solve(&formula, &bounds).expect("Failed to solve");
    // Should be UNSAT (theorem is provable)
    assert!(!solution.is_sat(), "COM008 conjecture check should be UNSAT");
}
