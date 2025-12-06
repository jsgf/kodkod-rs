//! MED001 - Medical domain base axioms
//!
//! A KK encoding of axioms MED001+0.ax and MED001+1.ax from http://www.cs.miami.edu/~tptp/
//! Base module for medical reasoning problems.
//!
//! Following Java: kodkod.examples.tptp.MED001

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct MED001 {
    pub bcapacityne: Relation,
    pub bcapacityex: Relation,
    pub bcapacitysn: Relation,
    pub conditionhyper: Relation,
    pub conditionhypo: Relation,
    pub conditionnormo: Relation,
    pub drugi: Relation,
    pub uptakelg: Relation,
    pub uptakepg: Relation,
    pub releaselg: Relation,
    pub bsecretioni: Relation,
    pub drugbg: Relation,
    pub qilt27: Relation,
    pub s0: Relation,
    pub s1: Relation,
    pub s2: Relation,
    pub s3: Relation,
    pub drugsu: Relation,
    pub n0: Relation,
    pub gt: Relation,
}

impl MED001 {
    pub fn new() -> Self {
        Self {
            bcapacityne: Relation::unary("bcapacityne"),
            bcapacityex: Relation::unary("bcapacityex"),
            bcapacitysn: Relation::unary("bcapacitysn"),
            conditionhyper: Relation::unary("conditionhyper"),
            conditionhypo: Relation::unary("conditionhypo"),
            conditionnormo: Relation::unary("conditionnormo"),
            drugi: Relation::unary("drugi"),
            uptakelg: Relation::unary("uptakelg"),
            uptakepg: Relation::unary("uptakepg"),
            releaselg: Relation::unary("releaselg"),
            bsecretioni: Relation::unary("bsecretioni"),
            drugbg: Relation::unary("drugbg"),
            qilt27: Relation::unary("qilt27"),
            s0: Relation::unary("s0"),
            s1: Relation::unary("s1"),
            s2: Relation::unary("s2"),
            s3: Relation::unary("s3"),
            drugsu: Relation::unary("drugsu"),
            n0: Relation::unary("n0"),
            gt: Relation::binary("gt"),
        }
    }

    /// Returns the declarations.
    pub fn decls(&self) -> Formula {
        Expression::from(self.n0.clone()).one()
    }

    /// Returns the irreflexivity_gt axiom.
    pub fn irreflexivity_gt(&self) -> Formula {
        Expression::from(self.gt.clone()).intersection(Expression::IDEN).no()
    }

    /// Returns the transitivity_gt axiom.
    pub fn transitivity_gt(&self) -> Formula {
        Expression::from(self.gt.clone())
            .join(Expression::from(self.gt.clone()))
            .in_set(Expression::from(self.gt.clone()))
    }

    /// Returns the axioms xorcapacity1 through xorcapacity1_4.
    pub fn xorcapacity1_4(&self) -> Formula {
        let bne = Expression::from(self.bcapacityne.clone());
        let bex = Expression::from(self.bcapacityex.clone());
        let bsn = Expression::from(self.bcapacitysn.clone());

        Expression::UNIV.in_set(bne.clone().union(bex.clone()).union(bsn.clone()))
            .and(bne.clone().intersection(bex.clone()).no())
            .and(bne.clone().intersection(bsn.clone()).no())
            .and(bex.intersection(bsn).no())
    }

    /// Returns the axioms xorcondition1 through xorcondition1_4.
    pub fn xorcondition1_4(&self) -> Formula {
        let hyper = Expression::from(self.conditionhyper.clone());
        let hypo = Expression::from(self.conditionhypo.clone());
        let normo = Expression::from(self.conditionnormo.clone());

        Expression::UNIV.in_set(hyper.clone().union(hypo.clone()).union(normo.clone()))
            .and(hyper.clone().intersection(hypo.clone()).no())
            .and(hyper.clone().intersection(normo.clone()).no())
            .and(normo.intersection(hypo).no())
    }

    /// Returns the insulin_effect axiom.
    pub fn insulin_effect(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f = x1.clone().in_set(Expression::from(self.drugi.clone()))
            .implies(x1.in_set(
                Expression::from(self.uptakelg.clone())
                    .intersection(Expression::from(self.uptakepg.clone()))
            ));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the liver_glucose axiom.
    pub fn liver_glucose(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f = x1.clone().in_set(Expression::from(self.uptakelg.clone()))
            .implies(x1.in_set(Expression::from(self.releaselg.clone())).not());

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the sulfonylurea_effect axiom.
    pub fn sulfonylurea_effect(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f = x1.clone().in_set(Expression::from(self.drugi.clone()))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacityex.clone())).not())
            .implies(x1.in_set(Expression::from(self.bsecretioni.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the biguanide_effect axiom.
    pub fn biguanide_effect(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f = x1.clone().in_set(Expression::from(self.drugbg.clone()))
            .implies(x1.in_set(Expression::from(self.releaselg.clone())).not());

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the sn_cure_1 axiom.
    pub fn sn_cure_1(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.bsecretioni.clone()))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacitysn.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.qilt27.clone())))
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(x1.in_set(Expression::from(self.conditionnormo.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the sn_cure_2 axiom.
    pub fn sn_cure_2(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.releaselg.clone())).not()
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacitysn.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.qilt27.clone())).not())
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(x1.in_set(Expression::from(self.conditionnormo.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the ne_cure axiom.
    pub fn ne_cure(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.releaselg.clone())).not()
            .or(x1.clone().in_set(Expression::from(self.uptakepg.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacityne.clone())))
            .and(x1.clone().in_set(Expression::from(self.bsecretioni.clone())))
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(x1.in_set(Expression::from(self.conditionnormo.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the ex_cure axiom.
    pub fn ex_cure(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.uptakelg.clone()))
            .and(x1.clone().in_set(Expression::from(self.uptakepg.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacityex.clone())).not())
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(x1.in_set(
            Expression::from(self.conditionnormo.clone())
                .union(Expression::from(self.conditionhypo.clone()))
        ));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the axioms xorstep1 through xorstep7.
    pub fn xorstep1_7(&self) -> Formula {
        let s0 = Expression::from(self.s0.clone());
        let s1 = Expression::from(self.s1.clone());
        let s2 = Expression::from(self.s2.clone());
        let s3 = Expression::from(self.s3.clone());

        Expression::UNIV.in_set(s0.clone().union(s1.clone()).union(s2.clone()).union(s3.clone()))
            .and(s0.clone().intersection(s1.clone()).no())
            .and(s0.clone().intersection(s2.clone()).no())
            .and(s0.clone().intersection(s3.clone()).no())
            .and(s1.clone().intersection(s2.clone()).no())
            .and(s1.clone().intersection(s3.clone()).no())
            .and(s2.intersection(s3).no())
    }

    /// Returns the normo axiom.
    pub fn normo(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.bsecretioni.clone()))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacitysn.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.qilt27.clone())))
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f1 = x1.clone().in_set(Expression::from(self.releaselg.clone())).not()
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacitysn.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.qilt27.clone())).not())
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f2 = x1.clone().in_set(Expression::from(self.releaselg.clone())).not()
            .or(x1.clone().in_set(Expression::from(self.uptakelg.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacitysn.clone())))
            .and(x1.clone().in_set(Expression::from(self.bsecretioni.clone())))
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f3 = x1.clone().in_set(Expression::from(self.uptakelg.clone()))
            .and(x1.clone().in_set(Expression::from(self.uptakepg.clone())))
            .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacityex.clone())))
            .and(Expression::from(x0.clone()).join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = x1.in_set(Expression::from(self.conditionnormo.clone()))
            .implies(f0.or(f1).or(f2).or(f3));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the axioms step1 through step4.
    pub fn step1_4(&self) -> Formula {
        let s1 = Expression::from(self.s1.clone());
        let s2 = Expression::from(self.s2.clone());
        let s3 = Expression::from(self.s3.clone());
        let qilt27 = Expression::from(self.qilt27.clone());
        let drugsu = Expression::from(self.drugsu.clone());
        let drugbg = Expression::from(self.drugbg.clone());
        let drugi = Expression::from(self.drugi.clone());

        s1.clone().intersection(qilt27.clone()).in_set(drugsu.clone())
            .and(s1.intersection(Expression::UNIV.difference(qilt27)).in_set(drugbg.clone()))
            .and(s2.in_set(drugbg.clone().intersection(drugsu.clone())))
            .and(s3.in_set(drugi.clone().intersection(drugsu.union(drugbg)).union(drugi)))
    }

    /// Returns the axioms sucomp and insulincomp.
    pub fn comp(&self) -> Formula {
        let s1 = Expression::from(self.s1.clone());
        let s2 = Expression::from(self.s2.clone());
        let s3 = Expression::from(self.s3.clone());
        let qilt27 = Expression::from(self.qilt27.clone());
        let drugsu = Expression::from(self.drugsu.clone());
        let drugi = Expression::from(self.drugi.clone());

        drugsu.in_set(s1.intersection(qilt27).union(s2).union(s3.clone()))
            .and(drugi.in_set(s3))
    }

    /// Returns the insulin_completion axiom.
    pub fn insulin_completion(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(
            Expression::from(self.uptakelg.clone())
                .union(Expression::from(self.uptakepg.clone()))
        );
        let f = f0.implies(x1.in_set(Expression::from(self.drugi.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the uptake_completion axiom.
    pub fn uptake_completion(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.releaselg.clone())).not();
        let f = f0.implies(x1.in_set(Expression::from(self.uptakelg.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the su_completion axiom.
    pub fn su_completion(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.bsecretioni.clone()));
        let f = f0.implies(
            x1.in_set(Expression::from(self.drugsu.clone()))
                .and(Expression::from(x0.clone()).in_set(Expression::from(self.bcapacityex.clone())).not())
        );

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the bg_completion axiom.
    pub fn bg_completion(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = x1.clone().in_set(Expression::from(self.releaselg.clone())).not();
        let f = f0.implies(x1.in_set(Expression::from(self.drugbg.clone())));

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the trans_ax1 axiom.
    pub fn trans_ax1(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = Expression::from(x0.clone()).in_set(Expression::from(self.s0.clone()))
            .and(x1.clone().in_set(Expression::from(self.conditionnormo.clone())).not());
        let f1 = x1.clone().intersection(Expression::from(self.s1.clone())).some()
            .and(x1.join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(f1);

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the trans_ax2 axiom.
    pub fn trans_ax2(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = Expression::from(x0.clone()).in_set(Expression::from(self.s1.clone()))
            .and(x1.clone().in_set(Expression::from(self.conditionnormo.clone())).not());
        let f1 = x1.clone().intersection(Expression::from(self.s2.clone()))
            .intersection(
                Expression::from(self.bcapacityne.clone())
                    .union(Expression::from(self.bcapacityex.clone()))
            )
            .some()
            .and(x1.join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(f1);

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the trans_ax3 axiom.
    pub fn trans_ax3(&self) -> Formula {
        let x0 = Variable::unary("X0");
        let x1 = Expression::UNIV.difference(Expression::from(x0.clone()).join(Expression::from(self.gt.clone())));

        let f0 = Expression::from(x0.clone()).in_set(Expression::from(self.s2.clone()))
            .and(x1.clone().in_set(Expression::from(self.conditionnormo.clone())).not());
        let f1 = x1.clone().intersection(Expression::from(self.s3.clone()))
            .intersection(Expression::from(self.bcapacityex.clone()))
            .some()
            .and(x1.join(Expression::from(self.gt.clone()))
                .in_set(Expression::from(self.conditionhyper.clone())));

        let f = f0.implies(f1);

        Formula::forall(Decls::from(Decl::one_of(x0, Expression::UNIV)), f)
    }

    /// Returns the conjunction of all axioms.
    pub fn axioms(&self) -> Formula {
        self.trans_ax2()
            .and(self.trans_ax3())
            .and(self.transitivity_gt())
            .and(self.decls())
            .and(self.irreflexivity_gt())
            .and(self.normo())
            .and(self.xorcapacity1_4())
            .and(self.xorcondition1_4())
            .and(self.insulin_effect())
            .and(self.liver_glucose())
            .and(self.sulfonylurea_effect())
            .and(self.biguanide_effect())
            .and(self.bg_completion())
            .and(self.sn_cure_1())
            .and(self.sn_cure_2())
            .and(self.ne_cure())
            .and(self.ex_cure())
            .and(self.su_completion())
            .and(self.xorstep1_7())
            .and(self.step1_4())
            .and(self.comp())
            .and(self.insulin_completion())
            .and(self.uptake_completion())
            .and(self.trans_ax1())
    }

    /// Returns bounds for the given scope.
    pub fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        let s = f.all(1);

        b.bound(&self.bcapacityne, f.none(1), s.clone())?;
        b.bound(&self.bcapacityex, f.none(1), s.clone())?;
        b.bound(&self.bcapacitysn, f.none(1), s.clone())?;
        b.bound(&self.conditionhyper, f.none(1), s.clone())?;
        b.bound(&self.conditionhypo, f.none(1), s.clone())?;
        b.bound(&self.conditionnormo, f.none(1), s.clone())?;
        b.bound(&self.drugi, f.none(1), s.clone())?;
        b.bound(&self.uptakelg, f.none(1), s.clone())?;
        b.bound(&self.uptakepg, f.none(1), s.clone())?;
        b.bound(&self.releaselg, f.none(1), s.clone())?;
        b.bound(&self.bsecretioni, f.none(1), s.clone())?;
        b.bound(&self.drugbg, f.none(1), s.clone())?;
        b.bound(&self.qilt27, f.none(1), s.clone())?;
        b.bound(&self.s0, f.none(1), s.clone())?;
        b.bound(&self.s1, f.none(1), s.clone())?;
        b.bound(&self.s2, f.none(1), s.clone())?;
        b.bound(&self.s3, f.none(1), s.clone())?;
        b.bound(&self.drugsu, f.none(1), s.clone())?;
        b.bound(&self.n0, f.none(1), s)?;
        b.bound(&self.gt, f.none(2), f.all(2))?;

        Ok(b)
    }
}

impl Default for MED001 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_med001 <scope>");
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

    let model = MED001::new();
    let formula = model.axioms();
    let bounds = model.bounds(n)?;

    println!("=== MED001 (scope={n}) ===\n");

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
fn test_med001_runs() {
    let model = MED001::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.axioms();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
