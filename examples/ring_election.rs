//! Ring Election Protocol
//!
//! Leader election algorithm in a ring topology.
//! Based on kodkod.examples.alloy.RingElection

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable, RelationPredicate};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct RingElection {
    // Main relations
    process: Relation,
    time: Relation,
    succ: Relation,
    to_send: Relation,
    elected: Relation,

    // Process ordering
    pfirst: Relation,
    plast: Relation,
    pord: Relation,

    // Time ordering
    tfirst: Relation,
    tlast: Relation,
    tord: Relation,
}

impl RingElection {
    fn new() -> Self {
        Self {
            process: Relation::unary("Process"),
            time: Relation::unary("Time"),
            succ: Relation::binary("succ"),
            to_send: Relation::ternary("toSend"),
            elected: Relation::binary("elected"),
            pfirst: Relation::unary("pfirst"),
            plast: Relation::unary("plast"),
            pord: Relation::binary("pord"),
            tfirst: Relation::unary("tfirst"),
            tlast: Relation::unary("tlast"),
            tord: Relation::binary("tord"),
        }
    }

    /// Declarations: Process and Time with total orderings, succ as function
    fn declarations(&self) -> Formula {
        let ord_time = Formula::RelationPredicate(RelationPredicate::TotalOrdering {
            relation: self.tord.clone(),
            ordered: self.time.clone(),
            first: self.tfirst.clone(),
            last: self.tlast.clone(),
        });

        let ord_process = Formula::RelationPredicate(RelationPredicate::TotalOrdering {
            relation: self.pord.clone(),
            ordered: self.process.clone(),
            first: self.pfirst.clone(),
            last: self.plast.clone(),
        });

        // succ is a function: Process -> Process
        // Manually encode: succ in Process->Process && all p: Process | one p.succ
        let succ_domain_range = Expression::from(self.succ.clone())
            .in_set(Expression::from(self.process.clone())
                .product(Expression::from(self.process.clone())));

        let p = Variable::unary("p_succ");
        let succ_functional = Formula::forall(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.process.clone()))),
            Expression::from(p).join(Expression::from(self.succ.clone())).one()
        );
        let succ_function = succ_domain_range.and(succ_functional);

        let elected_dom_range = Expression::from(self.elected.clone())
            .in_set(Expression::from(self.process.clone()).product(Expression::from(self.time.clone())));

        Formula::and_all(vec![ord_time, ord_process, succ_function, elected_dom_range])
    }

    /// fact Ring {all p: Process | Process in p.^succ}
    fn ring(&self) -> Formula {
        let p = Variable::unary("p");
        let body = Expression::from(self.process.clone())
            .in_set(Expression::from(p.clone()).join(Expression::from(self.succ.clone()).closure()));
        Formula::forall(Decls::from(Decl::one_of(p, Expression::from(self.process.clone()))), body)
    }

    /// pred init (t: Time) {all p: Process | p.toSend.t = p}
    fn init(&self, t: Expression) -> Formula {
        let p = Variable::unary("p");
        let body = Expression::from(p.clone())
            .join(Expression::from(self.to_send.clone()))
            .join(t)
            .equals(Expression::from(p.clone()));
        Formula::forall(Decls::from(Decl::one_of(p, Expression::from(self.process.clone()))), body)
    }

    /// Returns bounds for the given scope
    fn bounds(&self, processes: usize, times: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms = Vec::new();
        for i in 0..processes {
            atoms.push(format!("Process{}", i));
        }
        for i in 0..times {
            atoms.push(format!("Time{}", i));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // Process bounds
        let process_strs: Vec<String> = (0..processes).map(|i| format!("Process{}", i)).collect();
        let process_tuples: Vec<Vec<&str>> = process_strs.iter().map(|s| vec![s.as_str()]).collect();
        let process_refs: Vec<&[&str]> = process_tuples.iter().map(|v| v.as_slice()).collect();
        let process_bound = factory.tuple_set(&process_refs)?;

        // Time bounds
        let time_strs: Vec<String> = (0..times).map(|i| format!("Time{}", i)).collect();
        let time_tuples: Vec<Vec<&str>> = time_strs.iter().map(|s| vec![s.as_str()]).collect();
        let time_refs: Vec<&[&str]> = time_tuples.iter().map(|v| v.as_slice()).collect();
        let time_bound = factory.tuple_set(&time_refs)?;

        bounds.bound_exactly(&self.process, process_bound.clone())?;
        bounds.bound(&self.succ, factory.none(2), process_bound.product(&process_bound)?)?;
        bounds.bound(&self.to_send, factory.none(3),
            process_bound.product(&process_bound)?.product(&time_bound)?)?;
        bounds.bound(&self.elected, factory.none(2), process_bound.product(&time_bound)?)?;

        bounds.bound(&self.pord, factory.none(2), process_bound.product(&process_bound)?)?;
        bounds.bound_exactly(&self.pfirst, process_bound.clone())?;
        bounds.bound_exactly(&self.plast, process_bound)?;

        bounds.bound_exactly(&self.time, time_bound.clone())?;
        bounds.bound(&self.tord, factory.none(2), time_bound.product(&time_bound)?)?;
        bounds.bound_exactly(&self.tfirst, time_bound.clone())?;
        bounds.bound_exactly(&self.tlast, time_bound)?;

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Ring Election Protocol ===\n");

    let model = RingElection::new();
    let options = Options::default();

    // Test with larger scope to stress translation
    let processes = 5;
    let times = 5;

    println!("Configuration: {} processes, {} time steps", processes, times);

    let formula = model.declarations()
        .and(model.ring())
        .and(model.init(Expression::from(model.tfirst.clone())));
    let bounds = model.bounds(processes, times)?;

    println!("Solving...");
    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds)?;

    println!("Result: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });

    if solution.is_sat() {
        let stats = solution.statistics();
        println!("Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    }

    Ok(())
}
