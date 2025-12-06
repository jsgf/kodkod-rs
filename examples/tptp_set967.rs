//! SET967 - Set theory with cartesian products and ordered pairs
//!
//! A KK encoding of SET967+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.SET967

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct SET967 {
    pub empty: Relation,
    pub subset: Relation,
    pub in_rel: Relation,
    pub disjoint: Relation,
    pub union: Relation,
    pub singleton: Relation,
    pub intersect2: Relation,
    pub union2: Relation,
    pub cartesian2: Relation,
    pub ordered: Relation,
    pub unordered: Relation,
}

impl SET967 {
    pub fn new() -> Self {
        Self {
            empty: Relation::unary("empty"),
            subset: Relation::binary("subset"),
            in_rel: Relation::binary("in"),
            disjoint: Relation::binary("disjoint"),
            union: Relation::binary("union"),
            singleton: Relation::binary("singleton"),
            intersect2: Relation::ternary("set_intersection2"),
            union2: Relation::ternary("set_union2"),
            cartesian2: Relation::ternary("cartesian_product2"),
            ordered: Relation::ternary("ordered_pair"),
            unordered: Relation::ternary("unordered_pair"),
        }
    }

    fn set_intersection2(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.intersect2.clone())))
    }

    fn set_union2(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.union2.clone())))
    }

    fn cartesian_product2(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.cartesian2.clone())))
    }

    fn ordered_pair(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.ordered.clone())))
    }

    fn unordered_pair(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.unordered.clone())))
    }

    #[allow(dead_code)]
    fn union_of(&self, a: Expression) -> Expression {
        a.join(Expression::from(self.union.clone()))
    }

    fn singleton_of(&self, a: Expression) -> Expression {
        a.join(Expression::from(self.singleton.clone()))
    }

    fn is_empty(&self, a: Expression) -> Formula {
        a.in_set(Expression::from(self.empty.clone()))
    }

    fn in_set_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.in_rel.clone()))
    }

    fn disjoint_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.disjoint.clone()))
    }

    pub fn decls(&self) -> Formula {
        let f0 = self.union.clone().function(Expression::UNIV, Expression::UNIV);
        let f1 = self.singleton.clone().function(Expression::UNIV, Expression::UNIV);
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f2 = self.set_intersection2(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f3 = self.set_union2(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f4 = self.cartesian_product2(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f5 = self.ordered_pair(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f6 = self.unordered_pair(Expression::from(a.clone()), Expression::from(b.clone())).one();

        f0.and(f1).and(Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f2.and(f3).and(f4).and(f5).and(f6)
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

    pub fn commutativity_k2_tarski(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.unordered_pair(Expression::from(a.clone()), Expression::from(b.clone()))
            .equals(self.unordered_pair(Expression::from(b.clone()), Expression::from(a.clone())));
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

    pub fn d5_tarski(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f = self.ordered_pair(Expression::from(a.clone()), Expression::from(b.clone()))
            .equals(self.unordered_pair(
                self.unordered_pair(Expression::from(a.clone()), Expression::from(b.clone())),
                self.singleton_of(Expression::from(a.clone()))
            ));

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV)),
            f
        )
    }

    pub fn fc1_misc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let f = self.is_empty(self.ordered_pair(Expression::from(a.clone()), Expression::from(b.clone()))).not();
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

    pub fn a155_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let d = Variable::unary("D");

        let f0 = self.in_set_of(
            self.ordered_pair(Expression::from(a.clone()), Expression::from(b.clone())),
            self.cartesian_product2(Expression::from(c.clone()), Expression::from(d.clone()))
        );
        let f1 = self.in_set_of(Expression::from(a.clone()), Expression::from(c.clone()))
            .and(self.in_set_of(Expression::from(b.clone()), Expression::from(d.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV))
                .and(Decl::one_of(d, Expression::UNIV)),
            f0.iff(f1)
        )
    }

    pub fn rc1_xboole_0(&self) -> Formula {
        Expression::from(self.empty.clone()).some()
    }

    pub fn rc2_xboole_0(&self) -> Formula {
        Expression::UNIV.difference(Expression::from(self.empty.clone())).some()
    }

    pub fn t102_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");

        let f = self.in_set_of(
            Expression::from(a.clone()),
            self.cartesian_product2(Expression::from(b.clone()), Expression::from(c.clone()))
        ).implies(
            Expression::from(self.ordered.clone()).join(Expression::from(a.clone())).some()
        );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV)),
            f
        )
    }

    pub fn t107_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let d = Variable::unary("D");

        let f0 = self.in_set_of(
            self.ordered_pair(Expression::from(a.clone()), Expression::from(b.clone())),
            self.cartesian_product2(Expression::from(c.clone()), Expression::from(d.clone()))
        );
        let f1 = self.in_set_of(
            self.ordered_pair(Expression::from(b.clone()), Expression::from(a.clone())),
            self.cartesian_product2(Expression::from(d.clone()), Expression::from(c.clone()))
        );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV))
                .and(Decl::one_of(d, Expression::UNIV)),
            f0.iff(f1)
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

    pub fn t112_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let d = Variable::unary("D");

        let ordered = Expression::from(self.ordered.clone());

        let f0 = Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::UNIV)),
            self.in_set_of(Expression::from(c.clone()), Expression::from(a.clone()))
                .implies(ordered.clone().join(Expression::from(c.clone())).some())
        );

        let f1 = Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::UNIV)),
            self.in_set_of(Expression::from(c.clone()), Expression::from(b.clone()))
                .implies(ordered.clone().join(Expression::from(c.clone())).some())
        );

        let f2 = Formula::forall(
            Decls::from(Decl::one_of(c.clone(), Expression::UNIV))
                .and(Decl::one_of(d.clone(), Expression::UNIV)),
            self.in_set_of(
                self.ordered_pair(Expression::from(c.clone()), Expression::from(d.clone())),
                Expression::from(a.clone())
            ).iff(self.in_set_of(
                self.ordered_pair(Expression::from(c.clone()), Expression::from(d)),
                Expression::from(b.clone())
            ))
        );

        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::UNIV))
                .and(Decl::one_of(b.clone(), Expression::UNIV)),
            f0.and(f1).and(f2).implies(Expression::from(a).equals(Expression::from(b)))
        )
    }

    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.antisymmetry_r2_hidden())
            .and(self.commutativity_k2_xboole_0())
            .and(self.commutativity_k2_tarski())
            .and(self.d2_xboole_0())
            .and(self.d5_tarski())
            .and(self.fc1_misc_1())
            .and(self.fc2_xboole_0())
            .and(self.fc3_xboole_0())
            .and(self.idempotence_k2_xboole_0())
            .and(self.a155_zfmisc_1())
            .and(self.rc1_xboole_0())
            .and(self.rc2_xboole_0())
            .and(self.t102_zfmisc_1())
            .and(self.t107_zfmisc_1())
            .and(self.t4_xboole_0())
            .and(self.t112_zfmisc_1())
    }

    pub fn t120_zfmisc_1(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");

        let f0 = self.cartesian_product2(
            self.set_union2(Expression::from(a.clone()), Expression::from(b.clone())),
            Expression::from(c.clone())
        ).equals(self.set_union2(
            self.cartesian_product2(Expression::from(a.clone()), Expression::from(c.clone())),
            self.cartesian_product2(Expression::from(b.clone()), Expression::from(c.clone()))
        ));

        let f1 = self.cartesian_product2(
            Expression::from(c.clone()),
            self.set_union2(Expression::from(a.clone()), Expression::from(b.clone()))
        ).equals(self.set_union2(
            self.cartesian_product2(Expression::from(c.clone()), Expression::from(a.clone())),
            self.cartesian_product2(Expression::from(c.clone()), Expression::from(b.clone()))
        ));

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::UNIV))
                .and(Decl::one_of(b, Expression::UNIV))
                .and(Decl::one_of(c, Expression::UNIV)),
            f0.and(f1)
        )
    }

    pub fn check_t120_zfmisc_1(&self) -> Formula {
        self.axioms().and(self.t120_zfmisc_1().not())
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
        b.bound(&self.singleton, f.none(2), f.all(2))?;
        b.bound(&self.intersect2, f.none(3), f.all(3))?;
        b.bound(&self.cartesian2, f.none(3), f.all(3))?;
        b.bound(&self.union2, f.none(3), f.all(3))?;
        b.bound(&self.ordered, f.none(3), f.all(3))?;
        b.bound(&self.unordered, f.none(3), f.all(3))?;

        Ok(b)
    }
}

impl Default for SET967 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_set967 <scope>");
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

    let model = SET967::new();
    let formula = model.check_t120_zfmisc_1();
    let bounds = model.bounds(n)?;

    println!("=== SET967 (scope={n}) ===\n");

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
fn test_set967_runs() {
    let model = SET967::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_t120_zfmisc_1();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
