//! SET943 - Set theory axioms and conjecture
//!
//! A KK encoding of SET943+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.SET943

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct SET943 {
    pub empty: Relation,
    pub subset: Relation,
    pub in_rel: Relation,
    pub union: Relation,
    pub union2: Relation,
}

impl SET943 {
    pub fn new() -> Self {
        Self {
            empty: Relation::unary("empty"),
            subset: Relation::binary("subset"),
            in_rel: Relation::binary("in"),
            union: Relation::binary("union"),
            union2: Relation::ternary("set_union2"),
        }
    }

    /// Returns set_union2[A][B]
    fn set_union2(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.union2.clone())))
    }

    /// Returns union[a]
    fn union_of(&self, a: Expression) -> Expression {
        a.join(Expression::from(self.union.clone()))
    }

    /// Returns a in empty
    fn is_empty(&self, a: Expression) -> Formula {
        a.in_set(Expression::from(self.empty.clone()))
    }

    /// Returns a->b in subset
    fn subset_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.subset.clone()))
    }

    /// Returns a->b in in
    fn in_set_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.in_rel.clone()))
    }

    /// Returns the declarations.
    /// union is a function and set_union2[A][B] is one for all A, B
    pub fn decls(&self) -> Formula {
        let f0 = self.union.clone().function(Expression::univ(), Expression::univ());
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f1 = self.set_union2(Expression::from(a.clone()), Expression::from(b.clone())).one();
        f0.and(Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f1
        ))
    }

    /// Returns antisymmetry_r2_hidden axiom.
    /// all A, B | in(A,B) => !in(B,A)
    pub fn antisymmetry_r2_hidden(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.in_set_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .implies(self.in_set_of(Expression::from(b.clone()), Expression::from(a.clone())).not());
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns commutativity_k2_xboole_0 axiom.
    pub fn commutativity_k2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))
            .equals(self.set_union2(Expression::from(b.clone()), Expression::from(a.clone())));
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns d10_xboole_0 axiom.
    pub fn d10_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = Expression::from(a.clone()).equals(Expression::from(b.clone()))
            .iff(
                self.subset_of(Expression::from(a.clone()), Expression::from(b.clone()))
                    .and(self.subset_of(Expression::from(b.clone()), Expression::from(a.clone())))
            );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns d2_xboole_0 axiom.
    pub fn d2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let in_rel = Expression::from(self.in_rel.clone());

        let f = Expression::from(c.clone())
            .equals(self.set_union2(Expression::from(a.clone()), Expression::from(b.clone())))
            .iff(
                in_rel.clone().join(Expression::from(c.clone()))
                    .equals(
                        in_rel.clone().join(Expression::from(a.clone()))
                            .union(in_rel.join(Expression::from(b.clone())))
                    )
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ()))
                .and(Decl::one_of(c, Expression::univ())),
            f
        )
    }

    /// Returns d3_tarski axiom.
    pub fn d3_tarski(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let in_rel = Expression::from(self.in_rel.clone());

        let f = self.subset_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .iff(
                in_rel.clone().join(Expression::from(a.clone()))
                    .in_set(in_rel.join(Expression::from(b.clone())))
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns d4_tarski axiom.
    pub fn d4_tarski(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let in_rel = Expression::from(self.in_rel.clone());

        let f = Expression::from(b.clone())
            .equals(self.union_of(Expression::from(a.clone())))
            .iff(
                in_rel.clone().join(Expression::from(b.clone()))
                    .equals(in_rel.clone().join(in_rel.join(Expression::from(a.clone()))))
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns fc2_xboole_0 axiom.
    pub fn fc2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.is_empty(Expression::from(a.clone())).not()
            .implies(
                self.is_empty(self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))).not()
            );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns fc3_xboole_0 axiom.
    pub fn fc3_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.is_empty(Expression::from(a.clone())).not()
            .implies(
                self.is_empty(self.set_union2(Expression::from(b.clone()), Expression::from(a.clone()))).not()
            );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns idempotence_k2_xboole_0 axiom.
    pub fn idempotence_k2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let f = self.set_union2(Expression::from(a.clone()), Expression::from(a.clone()))
            .equals(Expression::from(a.clone()));
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ())),
            f
        )
    }

    /// Returns rc1_xboole_0 axiom.
    pub fn rc1_xboole_0(&self) -> Formula {
        Expression::from(self.empty.clone()).some()
    }

    /// Returns rc2_xboole_0 axiom.
    pub fn rc2_xboole_0(&self) -> Formula {
        Expression::univ().difference(Expression::from(self.empty.clone())).some()
    }

    /// Returns reflexivity_r1_tarski axiom.
    pub fn reflexivity_r1_tarski(&self) -> Formula {
        let a = Variable::unary("A");
        let f = self.subset_of(Expression::from(a.clone()), Expression::from(a.clone()));
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ())),
            f
        )
    }

    /// Returns t7_xboole_1 axiom.
    pub fn t7_xboole_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.subset_of(
            Expression::from(a.clone()),
            self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))
        );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns t8_xboole_1 axiom.
    pub fn t8_xboole_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");

        let f = self.subset_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .and(self.subset_of(Expression::from(c.clone()), Expression::from(b.clone())))
            .implies(
                self.subset_of(
                    self.set_union2(Expression::from(a.clone()), Expression::from(c.clone())),
                    Expression::from(b.clone())
                )
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ()))
                .and(Decl::one_of(c, Expression::univ())),
            f
        )
    }

    /// Returns t95_zfmisc_1 axiom.
    pub fn t95_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f = self.subset_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .implies(
                self.subset_of(
                    self.union_of(Expression::from(a.clone())),
                    self.union_of(Expression::from(b.clone()))
                )
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns the conjunction of all axioms.
    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.antisymmetry_r2_hidden())
            .and(self.commutativity_k2_xboole_0())
            .and(self.d10_xboole_0())
            .and(self.d2_xboole_0())
            .and(self.d3_tarski())
            .and(self.d4_tarski())
            .and(self.fc2_xboole_0())
            .and(self.fc3_xboole_0())
            .and(self.idempotence_k2_xboole_0())
            .and(self.rc1_xboole_0())
            .and(self.rc2_xboole_0())
            .and(self.reflexivity_r1_tarski())
            .and(self.t7_xboole_1())
            .and(self.t8_xboole_1())
            .and(self.t95_zfmisc_1())
    }

    /// Returns t96_zfmisc_1 conjecture.
    pub fn t96_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f = self.union_of(self.set_union2(Expression::from(a.clone()), Expression::from(b.clone())))
            .equals(self.set_union2(
                self.union_of(Expression::from(a.clone())),
                self.union_of(Expression::from(b.clone()))
            ));

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    pub fn check_t96_zfmisc_1(&self) -> Formula {
        self.axioms().and(self.t96_zfmisc_1().not())
    }

    /// Returns bounds for the given scope.
    pub fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        b.bound(&self.empty, f.none(1), f.all(1))?;
        b.bound(&self.subset, f.none(2), f.all(2))?;
        b.bound(&self.in_rel, f.none(2), f.all(2))?;
        b.bound(&self.union, f.none(2), f.all(2))?;
        b.bound(&self.union2, f.none(3), f.all(3))?;

        Ok(b)
    }
}

impl Default for SET943 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_set943 <scope>");
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

    let model = SET943::new();
    let formula = model.check_t96_zfmisc_1();
    let bounds = model.bounds(n)?;

    println!("=== SET943 (scope={n}) ===\n");

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
fn test_set943_runs() {
    let model = SET943::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_t96_zfmisc_1();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
