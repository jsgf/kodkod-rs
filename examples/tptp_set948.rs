//! SET948 - Set theory with intersection and union
//!
//! A KK encoding of SET948+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.SET948

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct SET948 {
    pub empty: Relation,
    pub subset: Relation,
    pub in_rel: Relation,
    pub disjoint: Relation,
    pub union: Relation,
    pub intersect2: Relation,
    pub union2: Relation,
}

impl SET948 {
    pub fn new() -> Self {
        Self {
            empty: Relation::unary("empty"),
            subset: Relation::binary("subset"),
            in_rel: Relation::binary("in"),
            disjoint: Relation::binary("disjoint"),
            union: Relation::binary("union"),
            intersect2: Relation::ternary("set_intersection2"),
            union2: Relation::ternary("set_union2"),
        }
    }

    fn set_intersection2(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.intersect2.clone())))
    }

    fn set_union2(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.union2.clone())))
    }

    fn union_of(&self, a: Expression) -> Expression {
        a.join(Expression::from(self.union.clone()))
    }

    fn is_empty(&self, a: Expression) -> Formula {
        a.in_set(Expression::from(self.empty.clone()))
    }

    fn subset_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.subset.clone()))
    }

    fn in_set_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.in_rel.clone()))
    }

    fn disjoint_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.disjoint.clone()))
    }

    pub fn decls(&self) -> Formula {
        let f0 = self.union.clone().function(Expression::UNIV, Expression::UNIV);
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f1 = self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f2 = self.set_union2(Expression::from(a.clone()), Expression::from(b.clone())).one();
        f0.and(Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f1.and(f2)
        ))
    }

    pub fn antisymmetry_r2_hidden(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.in_set_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .implies(self.in_set_of(Expression::from(b.clone()), Expression::from(a.clone())).not());
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn commutativity_k2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))
            .equals(self.set_union2(Expression::from(b.clone()), Expression::from(a.clone())));
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn d10_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = Expression::from(a.clone()).equals(Expression::from(b.clone()))
            .iff(
                self.subset_of(Expression::from(a.clone()), Expression::from(b.clone()))
                    .and(self.subset_of(Expression::from(b.clone()), Expression::from(a.clone())))
            );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

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
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV)),
            f
        )
    }

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
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn d3_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let in_rel = Expression::from(self.in_rel.clone());

        let f = Expression::from(c.clone())
            .equals(self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone())))
            .iff(
                in_rel.clone().join(Expression::from(c.clone()))
                    .equals(
                        in_rel.clone().join(Expression::from(a.clone()))
                            .intersection(in_rel.join(Expression::from(b.clone())))
                    )
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV)),
            f
        )
    }

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
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn fc2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.is_empty(Expression::from(a.clone())).not()
            .implies(
                self.is_empty(self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))).not()
            );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn fc3_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.is_empty(Expression::from(a.clone())).not()
            .implies(
                self.is_empty(self.set_union2(Expression::from(b.clone()), Expression::from(a.clone()))).not()
            );
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn idempotence_k2_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let f = self.set_union2(Expression::from(a.clone()), Expression::from(a.clone()))
            .equals(Expression::from(a.clone()));
        Formula::forall(Decls::from(Decl::one_of(a, Expression::UNIV)), f)
    }

    pub fn idempotence_k3_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let f = self.set_intersection2(Expression::from(a.clone()), Expression::from(a.clone()))
            .equals(Expression::from(a.clone()));
        Formula::forall(Decls::from(Decl::one_of(a, Expression::UNIV)), f)
    }

    pub fn rc1_xboole_0(&self) -> Formula {
        Expression::from(self.empty.clone()).some()
    }

    pub fn rc2_xboole_0(&self) -> Formula {
        Expression::UNIV.difference(Expression::from(self.empty.clone())).some()
    }

    pub fn reflexivity_r1_tarski(&self) -> Formula {
        let a = Variable::unary("A");
        let f = self.subset_of(Expression::from(a.clone()), Expression::from(a.clone()));
        Formula::forall(Decls::from(Decl::one_of(a, Expression::UNIV)), f)
    }

    pub fn symmetry_r1_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.disjoint_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .implies(self.disjoint_of(Expression::from(b.clone()), Expression::from(a.clone())));
        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn t4_xboole_0(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f = self.disjoint_of(Expression::from(a.clone()), Expression::from(b.clone())).not()
            .implies(
                self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone())).some()
            )
            .and(
                self.disjoint_of(Expression::from(a.clone()), Expression::from(b.clone()))
                    .implies(
                        self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone())).no()
                    )
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn t97_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f = self.subset_of(
            self.union_of(self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone()))),
            self.set_intersection2(
                self.union_of(Expression::from(a.clone())),
                self.union_of(Expression::from(b.clone()))
            )
        );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.antisymmetry_r2_hidden())
            .and(self.commutativity_k2_xboole_0())
            .and(self.d10_xboole_0())
            .and(self.d2_xboole_0())
            .and(self.d3_tarski())
            .and(self.d3_xboole_0())
            .and(self.d4_tarski())
            .and(self.fc2_xboole_0())
            .and(self.fc3_xboole_0())
            .and(self.idempotence_k2_xboole_0())
            .and(self.idempotence_k3_xboole_0())
            .and(self.rc1_xboole_0())
            .and(self.rc2_xboole_0())
            .and(self.reflexivity_r1_tarski())
            .and(self.symmetry_r1_xboole_0())
            .and(self.t4_xboole_0())
            .and(self.t97_zfmisc_1())
    }

    pub fn t101_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let d = Variable::unary("D");

        let f0 = self.in_set_of(
            Expression::from(c.clone()).union(Expression::from(d.clone())),
            self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))
        )
        .implies(
            Expression::from(c.clone()).equals(Expression::from(d.clone()))
                .or(self.disjoint_of(Expression::from(c.clone()), Expression::from(c.clone())))
        );

        let f0_forall = Formula::forall(
            Decls::from(Decl::one_of(c, Expression::UNIV))
                .and(Decl::one_of(d, Expression::UNIV)),
            f0
        );

        let f1 = self.union_of(self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone())))
            .equals(self.set_intersection2(
                self.union_of(Expression::from(a.clone())),
                self.union_of(Expression::from(b.clone()))
            ));

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f0_forall.implies(f1)
        )
    }

    pub fn check_t101_zfmisc_1(&self) -> Formula {
        self.axioms().and(self.t101_zfmisc_1().not())
    }

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
        b.bound(&self.disjoint, f.none(2), f.all(2))?;
        b.bound(&self.union, f.none(2), f.all(2))?;
        b.bound(&self.intersect2, f.none(3), f.all(3))?;
        b.bound(&self.union2, f.none(3), f.all(3))?;

        Ok(b)
    }
}

impl Default for SET948 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_set948 <scope>");
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

    let model = SET948::new();
    let formula = model.check_t101_zfmisc_1();
    let bounds = model.bounds(n)?;

    println!("=== SET948 (scope={n}) ===\n");

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
fn test_set948_runs() {
    let model = SET948::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_t101_zfmisc_1();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
