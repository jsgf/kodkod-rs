//! TOP020 - Topology: Hausdorff spaces and diagonal closed theorem
//!
//! A KK encoding of TOP020+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.TOP020

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct TOP020 {
    pub hausdorff: Relation,
    pub member: Relation,
    pub open: Relation,
    pub disjoint: Relation,
    pub closed: Relation,
    pub coerce: Relation,
    pub diagonal: Relation,
    pub product: Relation,
    pub tsproduct: Relation,
    pub ordered: Relation,
}

impl TOP020 {
    pub fn new() -> Self {
        Self {
            hausdorff: Relation::unary("a_hausdorff_top_space"),
            member: Relation::binary("a_member_of"),
            open: Relation::binary("open_in"),
            disjoint: Relation::binary("disjoint"),
            closed: Relation::binary("closed_in"),
            coerce: Relation::binary("coerce_to_class"),
            diagonal: Relation::binary("the_diagonal_top"),
            product: Relation::ternary("the_product_of"),
            tsproduct: Relation::ternary("the_product_top_space_of"),
            ordered: Relation::ternary("ordered_pair"),
        }
    }

    /// Returns the_product_top_space_of[A][B]
    fn the_product_top_space_of(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.tsproduct.clone())))
    }

    /// Returns the_product_of[A][B]
    fn the_product_of(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.product.clone())))
    }

    /// Returns the_ordered_pair[A][B]
    fn the_ordered_pair(&self, a: Expression, b: Expression) -> Expression {
        b.join(a.join(Expression::from(self.ordered.clone())))
    }

    /// Returns coerce_to_class[A]
    fn coerce_to_class(&self, a: Expression) -> Expression {
        a.join(Expression::from(self.coerce.clone()))
    }

    /// Returns the_diagonal_top[A]
    fn the_diagonal_top(&self, a: Expression) -> Expression {
        a.join(Expression::from(self.diagonal.clone()))
    }

    /// Returns a->b in a_member_of
    fn a_member_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.member.clone()))
    }

    /// Returns a->b in open_in
    fn open_in(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.open.clone()))
    }

    /// Returns a->b in closed_in
    fn closed_in(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.closed.clone()))
    }

    /// Returns a->b in disjoint
    fn disjoint_of(&self, a: Expression, b: Expression) -> Formula {
        a.product(b).in_set(Expression::from(self.disjoint.clone()))
    }

    /// Returns the declarations.
    pub fn decls(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let f0 = self.coerce.clone().function(Expression::univ(), Expression::univ());
        let f1 = self.diagonal.clone().function(Expression::univ(), Expression::univ());

        let f2 = self.the_product_top_space_of(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f2 = Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::univ()))
                .and(Decl::one_of(b.clone(), Expression::univ())),
            f2
        );

        let f3 = self.the_product_of(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f3 = Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::univ()))
                .and(Decl::one_of(b.clone(), Expression::univ())),
            f3
        );

        let f4 = self.the_ordered_pair(Expression::from(a.clone()), Expression::from(b.clone())).one();
        let f4 = Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f4
        );

        f0.and(f1).and(f2).and(f3).and(f4)
    }

    /// Returns closed_subset_thm axiom.
    pub fn closed_subset_thm(&self) -> Formula {
        let x = Variable::unary("X");
        let a = Variable::unary("A");
        let y = Variable::unary("Y");

        let member = Expression::from(self.member.clone());
        let open = Expression::from(self.open.clone());
        let disjoint = Expression::from(self.disjoint.clone());

        let f0 = self.a_member_of(Expression::from(y.clone()), self.coerce_to_class(Expression::from(x.clone())))
            .and(self.a_member_of(Expression::from(y.clone()), Expression::from(a.clone())).not());

        let f1 = Expression::from(y.clone()).join(member)
            .intersection(open.join(Expression::from(x.clone())))
            .intersection(disjoint.join(Expression::from(a.clone())))
            .some();

        let f2 = Formula::forall(
            Decls::from(Decl::one_of(y, Expression::univ())),
            f0.implies(f1)
        );

        let result = f2.implies(self.closed_in(Expression::from(a.clone()), Expression::from(x.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::univ()))
                .and(Decl::one_of(a, Expression::univ())),
            result
        )
    }

    /// Returns hausdorff axiom.
    pub fn hausdorff(&self) -> Formula {
        let x = Variable::unary("X");
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let open = Expression::from(self.open.clone());
        let member = Expression::from(self.member.clone());
        let disjoint = Expression::from(self.disjoint.clone());

        let g1 = open.clone().join(Expression::from(x.clone()))
            .intersection(Expression::from(a.clone()).join(member.clone()));
        let g2 = open.join(Expression::from(x.clone()))
            .intersection(Expression::from(b.clone()).join(member.clone()));
        let abrange = member.join(self.coerce_to_class(Expression::from(x.clone())));

        let inner = Expression::from(a.clone()).equals(Expression::from(b.clone())).not()
            .implies(g1.product(g2).intersection(disjoint).some());

        let inner_forall = Formula::forall(
            Decls::from(Decl::one_of(a, abrange.clone()))
                .and(Decl::one_of(b, abrange)),
            inner
        );

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::from(self.hausdorff.clone()))),
            inner_forall
        )
    }

    /// Returns product_of_open_sets axiom.
    pub fn product_of_open_sets(&self) -> Formula {
        let a = Variable::unary("A");
        let x = Variable::unary("X");
        let b = Variable::unary("B");
        let y = Variable::unary("Y");

        let f0 = self.open_in(Expression::from(a.clone()), Expression::from(x.clone()))
            .and(self.open_in(Expression::from(b.clone()), Expression::from(y.clone())));
        let f1 = self.open_in(
            self.the_product_of(Expression::from(a.clone()), Expression::from(b.clone())),
            self.the_product_top_space_of(Expression::from(x.clone()), Expression::from(y.clone()))
        );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(x, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ()))
                .and(Decl::one_of(y, Expression::univ())),
            f0.implies(f1)
        )
    }

    /// Returns product_top axiom.
    pub fn product_top(&self) -> Formula {
        let s = Variable::unary("S");
        let t = Variable::unary("T");
        let x = Variable::unary("X");

        let member = Expression::from(self.member.clone());
        let ordered = Expression::from(self.ordered.clone());

        let f0 = self.a_member_of(
            Expression::from(x.clone()),
            self.coerce_to_class(self.the_product_top_space_of(
                Expression::from(s.clone()),
                Expression::from(t.clone())
            ))
        );

        let e0 = member.clone().join(self.coerce_to_class(Expression::from(s.clone())));
        let e1 = member.join(self.coerce_to_class(Expression::from(t.clone())));
        let f1 = ordered.intersection(e0.product(e1).product(Expression::from(x.clone()))).some();

        Formula::forall(
            Decls::from(Decl::one_of(s, Expression::univ()))
                .and(Decl::one_of(t, Expression::univ()))
                .and(Decl::one_of(x, Expression::univ())),
            f0.implies(f1)
        )
    }

    /// Returns product axiom.
    pub fn product(&self) -> Formula {
        let x = Variable::unary("X");
        let s = Variable::unary("S");
        let t = Variable::unary("T");

        let member = Expression::from(self.member.clone());
        let ordered = Expression::from(self.ordered.clone());

        let f0 = self.a_member_of(
            Expression::from(x.clone()),
            self.the_product_of(Expression::from(s.clone()), Expression::from(t.clone()))
        );

        let e0 = member.clone().join(Expression::from(s.clone()));
        let e1 = member.join(Expression::from(t.clone()));
        let f1 = ordered.intersection(e0.product(e1).product(Expression::from(x.clone()))).some();

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::univ()))
                .and(Decl::one_of(s, Expression::univ()))
                .and(Decl::one_of(t, Expression::univ())),
            f0.iff(f1)
        )
    }

    /// Returns disjoint_defn axiom.
    pub fn disjoint_defn(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");

        let member = Expression::from(self.member.clone());

        let f = self.disjoint_of(Expression::from(a.clone()), Expression::from(b.clone()))
            .iff(
                member.clone().join(Expression::from(a.clone()))
                    .intersection(member.join(Expression::from(b.clone())))
                    .no()
            );

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ())),
            f
        )
    }

    /// Returns ordered_pair axiom.
    pub fn ordered_pair(&self) -> Formula {
        let a = Variable::unary("A");
        let b = Variable::unary("B");
        let c = Variable::unary("C");
        let d = Variable::unary("D");

        let f0 = self.the_ordered_pair(Expression::from(a.clone()), Expression::from(b.clone()))
            .equals(self.the_ordered_pair(Expression::from(c.clone()), Expression::from(d.clone())));
        let f1 = Expression::from(a.clone()).equals(Expression::from(c.clone()))
            .and(Expression::from(b.clone()).equals(Expression::from(d.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(a, Expression::univ()))
                .and(Decl::one_of(b, Expression::univ()))
                .and(Decl::one_of(c, Expression::univ()))
                .and(Decl::one_of(d, Expression::univ())),
            f0.implies(f1)
        )
    }

    /// Returns diagonal_top axiom.
    pub fn diagonal_top(&self) -> Formula {
        let x = Variable::unary("X");
        let s = Variable::unary("S");

        let member = Expression::from(self.member.clone());
        let ordered = Expression::from(self.ordered.clone());

        let f0 = self.a_member_of(
            Expression::from(x.clone()),
            self.coerce_to_class(self.the_diagonal_top(Expression::from(s.clone())))
        );

        let a_set = member.join(self.coerce_to_class(Expression::from(s.clone())));
        let f1 = ordered.intersection(
            a_set.clone().product(a_set).intersection(Expression::iden()).product(Expression::from(x.clone()))
        ).some();

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::univ()))
                .and(Decl::one_of(s, Expression::univ())),
            f0.iff(f1)
        )
    }

    /// Returns the conjunction of all axioms.
    pub fn axioms(&self) -> Formula {
        self.decls()
            .and(self.closed_subset_thm())
            .and(self.hausdorff())
            .and(self.product_of_open_sets())
            .and(self.product_top())
            .and(self.product())
            .and(self.disjoint_defn())
            .and(self.ordered_pair())
            .and(self.diagonal_top())
    }

    /// Returns challenge_AMR_1_4_4 conjecture.
    pub fn challenge_amr_1_4_4(&self) -> Formula {
        let s = Variable::unary("S");

        let f = self.closed_in(
            self.coerce_to_class(self.the_diagonal_top(Expression::from(s.clone()))),
            self.the_product_top_space_of(Expression::from(s.clone()), Expression::from(s.clone()))
        );

        Formula::forall(
            Decls::from(Decl::one_of(s, Expression::from(self.hausdorff.clone()))),
            f
        )
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    pub fn check_challenge_amr_1_4_4(&self) -> Formula {
        self.axioms().and(self.challenge_amr_1_4_4().not())
    }

    /// Returns bounds for the given scope.
    pub fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        b.bound(&self.hausdorff, f.none(1), f.all(1))?;
        b.bound(&self.member, f.none(2), f.all(2))?;
        b.bound(&self.open, f.none(2), f.all(2))?;
        b.bound(&self.disjoint, f.none(2), f.all(2))?;
        b.bound(&self.closed, f.none(2), f.all(2))?;
        b.bound(&self.coerce, f.none(2), f.all(2))?;
        b.bound(&self.diagonal, f.none(2), f.all(2))?;
        b.bound(&self.product, f.none(3), f.all(3))?;
        b.bound(&self.tsproduct, f.none(3), f.all(3))?;
        b.bound(&self.ordered, f.none(3), f.all(3))?;

        Ok(b)
    }
}

impl Default for TOP020 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_top020 <scope>");
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

    let model = TOP020::new();
    let formula = model.check_challenge_amr_1_4_4();
    let bounds = model.bounds(n)?;

    println!("=== TOP020 (scope={n}) ===\n");

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
fn test_top020_runs() {
    let model = TOP020::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_challenge_amr_1_4_4();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
