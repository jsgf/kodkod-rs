//! MGT066 - Management theory ordering axioms
//!
//! A KK encoding of MGT066+1.p from http://www.cs.miami.edu/~tptp/
//!
//! Following Java: kodkod.examples.tptp.MGT066

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct MGT066 {
    pub lt: Relation,
    pub leq: Relation,
    pub gt: Relation,
    pub geq: Relation,
}

impl MGT066 {
    pub fn new() -> Self {
        Self {
            lt: Relation::binary("smaller"),
            leq: Relation::binary("smaller_or_equal"),
            gt: Relation::binary("greater"),
            geq: Relation::binary("greater_or_equal"),
        }
    }

    /// Returns the definition_smaller_or_equal axiom.
    /// leq = lt + iden
    pub fn definition_smaller_or_equal(&self) -> Formula {
        Expression::from(self.leq.clone()).equals(
            Expression::from(self.lt.clone()).union(Expression::iden())
        )
    }

    /// Returns the definition_greater_or_equal axiom.
    /// geq = gt + iden
    pub fn definition_greater_or_equal(&self) -> Formula {
        Expression::from(self.geq.clone()).equals(
            Expression::from(self.gt.clone()).union(Expression::iden())
        )
    }

    /// Returns definition_smaller axiom.
    /// lt = ~gt
    pub fn definition_smaller(&self) -> Formula {
        Expression::from(self.lt.clone()).equals(
            Expression::from(self.gt.clone()).transpose()
        )
    }

    /// Returns meaning_postulate_greater_strict axiom.
    /// no (gt & ~gt)
    pub fn meaning_postulate_greater_strict(&self) -> Formula {
        Expression::from(self.gt.clone())
            .intersection(Expression::from(self.gt.clone()).transpose())
            .no()
    }

    /// Returns meaning_postulate_greater_transitive.
    /// gt.gt in gt
    pub fn meaning_postulate_greater_transitive(&self) -> Formula {
        Expression::from(self.gt.clone())
            .join(Expression::from(self.gt.clone()))
            .in_set(Expression::from(self.gt.clone()))
    }

    /// Returns meaning_postulate_greater_comparable.
    /// all x, y: UNIV | x = y or y in x.lt or x in y.lt
    pub fn meaning_postulate_greater_comparable(&self) -> Formula {
        let x = Variable::unary("X");
        let y = Variable::unary("Y");

        let f = Expression::from(x.clone()).equals(Expression::from(y.clone()))
            .or(Expression::from(y.clone()).in_set(
                Expression::from(x.clone()).join(Expression::from(self.lt.clone()))
            ))
            .or(Expression::from(x.clone()).in_set(
                Expression::from(y.clone()).join(Expression::from(self.lt.clone()))
            ));

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::univ()))
                .and(Decl::one_of(y, Expression::univ())),
            f
        )
    }

    /// Returns the conjunction of all axioms.
    pub fn axioms(&self) -> Formula {
        self.definition_smaller()
            .and(self.definition_smaller_or_equal())
            .and(self.definition_greater_or_equal())
            .and(self.meaning_postulate_greater_comparable())
            .and(self.meaning_postulate_greater_strict())
            .and(self.meaning_postulate_greater_transitive())
    }

    /// Returns bounds for the given scope.
    pub fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        let all2 = f.all(2);
        b.bound(&self.lt, f.none(2), all2.clone())?;
        b.bound(&self.leq, f.none(2), all2.clone())?;
        b.bound(&self.gt, f.none(2), all2.clone())?;
        b.bound(&self.geq, f.none(2), all2)?;

        Ok(b)
    }
}

impl Default for MGT066 {
    fn default() -> Self {
        Self::new()
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_mgt066 <scope>");
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

    let model = MGT066::new();
    let formula = model.axioms();
    let bounds = model.bounds(n)?;

    println!("=== MGT066 (scope={n}) ===\n");

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
fn test_mgt066_runs() {
    let model = MGT066::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.axioms();
    let solution = solver.solve(&formula, &bounds).expect("Failed to solve");
    assert!(solution.is_sat(), "MGT066 axioms should be SAT");
}
