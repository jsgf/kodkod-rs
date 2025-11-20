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

    /// pred step (t, t': Time, p: Process) {
    ///   let from = p.toSend, to = p.succ.toSend |
    ///    some id: from.t {
    ///     from.t' = from.t - id
    ///     to.t' = to.t + (id - PO/prevs(p.succ)) } }
    fn step(&self, t1: Expression, t2: Expression, p: Expression) -> Formula {
        let from = p.clone().join(Expression::from(self.to_send.clone()));
        let to = p.clone().join(Expression::from(self.succ.clone()))
            .join(Expression::from(self.to_send.clone()));

        let id = Variable::unary("id");
        let prevs = p.join(Expression::from(self.succ.clone()))
            .join(Expression::from(self.pord.clone()).transpose().closure());

        let f1 = from.clone().join(t2.clone())
            .equals(from.clone().join(t1.clone()).difference(Expression::from(id.clone())));
        let f2 = to.clone().join(t2.clone())
            .equals(to.clone().join(t1.clone()).union(Expression::from(id.clone()).difference(prevs)));

        let body = f1.and(f2);
        Formula::exists(Decls::from(Decl::one_of(id, from.join(t1))), body)
    }

    /// pred skip (t, t': Time, p: Process) {p.toSend.t = p.toSend.t'}
    fn skip(&self, t1: Expression, t2: Expression, p: Expression) -> Formula {
        p.clone().join(Expression::from(self.to_send.clone())).join(t1)
            .equals(p.join(Expression::from(self.to_send.clone())).join(t2))
    }

    /// fact Traces {
    ///   init (TO/first ())
    ///   all t: Time - TO/last() | let t' = TO/next (t) |
    ///    all p: Process | step (t, t', p) or step (t, t', succ.p) or skip (t, t', p) }
    fn traces(&self) -> Formula {
        let t1 = Variable::unary("t");
        let t2 = Expression::from(t1.clone()).join(Expression::from(self.tord.clone()));
        let p = Variable::unary("p");

        let f = self.step(Expression::from(t1.clone()), t2.clone(), Expression::from(p.clone()))
            .or(self.step(Expression::from(t1.clone()), t2.clone(),
                Expression::from(self.succ.clone()).join(Expression::from(p.clone()))))
            .or(self.skip(Expression::from(t1.clone()), t2, Expression::from(p.clone())));

        let f_all = Formula::forall(
            Decls::from(Decl::one_of(p, Expression::from(self.process.clone()))),
            f
        );
        let f_all_times = Formula::forall(
            Decls::from(Decl::one_of(t1, Expression::from(self.time.clone())
                .difference(Expression::from(self.tlast.clone())))),
            f_all
        );

        self.init(Expression::from(self.tfirst.clone())).and(f_all_times)
    }

    /// fact DefineElected {
    ///   no elected.TO/first()
    ///   all t: Time - TO/first()|
    ///    elected.t = {p: Process | p in p.toSend.t - p.toSend.(TO/prev(t))} }
    fn define_elected(&self) -> Formula {
        let f1 = Expression::from(self.elected.clone())
            .join(Expression::from(self.tfirst.clone()))
            .no();

        let t = Variable::unary("t");
        let p = Variable::unary("p");

        let condition = Expression::from(p.clone()).in_set(
            Expression::from(p.clone()).join(Expression::from(self.to_send.clone()))
                .join(Expression::from(t.clone()))
                .difference(
                    Expression::from(p.clone()).join(Expression::from(self.to_send.clone()))
                        .join(Expression::from(t.clone()).join(Expression::from(self.tord.clone()).transpose()))
                )
        );

        let comprehension = condition.comprehension(
            Decls::from(Decl::one_of(p, Expression::from(self.process.clone())))
        );

        let f2 = Expression::from(self.elected.clone()).join(Expression::from(t.clone()))
            .equals(comprehension);

        let f2_all = Formula::forall(
            Decls::from(Decl::one_of(t, Expression::from(self.time.clone())
                .difference(Expression::from(self.tfirst.clone())))),
            f2
        );

        f1.and(f2_all)
    }

    /// pred progress () {
    ///   all t: Time - TO/last() | let t' = TO/next (t) |
    ///    some Process.toSend.t => some p: Process | not skip (t, t', p) }
    fn progress(&self) -> Formula {
        let t1 = Variable::unary("t");
        let t2 = Expression::from(t1.clone()).join(Expression::from(self.tord.clone()));
        let p = Variable::unary("p");

        let condition = Expression::from(self.process.clone())
            .join(Expression::from(self.to_send.clone()))
            .join(Expression::from(t1.clone()))
            .some();

        let consequent = Formula::exists(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.process.clone()))),
            self.skip(Expression::from(t1.clone()), t2, Expression::from(p)).not()
        );

        let f1 = condition.implies(consequent);

        Formula::forall(
            Decls::from(Decl::one_of(t1, Expression::from(self.time.clone())
                .difference(Expression::from(self.tlast.clone())))),
            f1
        )
    }

    /// pred looplessPath () {no disj t, t': Time | toSend.t = toSend.t'}
    fn loopless_path(&self) -> Formula {
        let t1 = Variable::unary("t");
        let t2 = Variable::unary("t'");

        let f1 = Expression::from(t1.clone()).intersection(Expression::from(t2.clone())).some()
            .or(Expression::from(self.to_send.clone()).join(Expression::from(t1.clone()))
                .equals(Expression::from(self.to_send.clone()).join(Expression::from(t2.clone())))
                .not());

        Formula::forall(
            Decls::from(Decl::one_of(t1, Expression::from(self.time.clone())))
                .and(Decl::one_of(t2, Expression::from(self.time.clone()))),
            f1
        )
    }

    /// assert AtLeastOneElected { progress () => some elected.Time }
    fn at_least_one_elected(&self) -> Formula {
        self.progress().implies(
            Expression::from(self.elected.clone())
                .join(Expression::from(self.time.clone()))
                .some()
        )
    }

    /// assert AtMostOneElected {lone elected.Time}
    fn at_most_one_elected(&self) -> Formula {
        Expression::from(self.elected.clone())
            .join(Expression::from(self.time.clone()))
            .lone()
    }

    /// Returns the declarations and facts of the model
    fn invariants(&self) -> Formula {
        self.declarations()
            .and(self.ring())
            .and(self.traces())
            .and(self.define_elected())
    }

    /// Returns the conjunction of the invariants and the negation of atMostOneElected
    fn check_at_most_one_elected(&self) -> Formula {
        self.invariants().and(self.at_most_one_elected().not())
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

        // Ordering relations: pord, pfirst, plast can be any subset of process bounds
        bounds.bound(&self.pord, factory.none(2), process_bound.product(&process_bound)?)?;
        bounds.bound(&self.pfirst, factory.none(1), process_bound.clone())?;
        bounds.bound(&self.plast, factory.none(1), process_bound)?;

        bounds.bound_exactly(&self.time, time_bound.clone())?;
        bounds.bound(&self.tord, factory.none(2), time_bound.product(&time_bound)?)?;
        bounds.bound(&self.tfirst, factory.none(1), time_bound.clone())?;
        bounds.bound(&self.tlast, factory.none(1), time_bound)?;

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Ring Election Protocol ===\n");

    let model = RingElection::new();
    let options = Options::default();

    // Test 1: check AtMostOneElected for 3 Process, 7 Time (from Alloy line 65)
    println!("Test 1: Check AtMostOneElected for 3 Process, 7 Time");
    println!("Formula: invariants && !atMostOneElected\n");

    let formula1 = model.check_at_most_one_elected();
    let bounds1 = model.bounds(3, 7)?;

    let solver = Solver::new(options);
    let solution1 = solver.solve(&formula1, &bounds1)?;

    println!("Result: {}", if solution1.is_sat() { "SAT (counterexample found)" } else { "UNSAT (property holds)" });
    let stats1 = solution1.statistics();
    println!("  Variables: {}, Clauses: {}", stats1.num_variables(), stats1.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms\n",
        stats1.translation_time(), stats1.solving_time(), stats1.total_time());

    // Test 2: check AtLeastOneElected with progress (from Alloy line 59)
    println!("Test 2: Check AtLeastOneElected (with progress) for 3 Process, 7 Time");
    println!("Formula: invariants && !(progress => some elected.Time)\n");

    let formula2 = model.invariants().and(model.at_least_one_elected().not());
    let bounds2 = model.bounds(3, 7)?;
    let solution2 = solver.solve(&formula2, &bounds2)?;

    println!("Result: {}", if solution2.is_sat() { "SAT (counterexample found)" } else { "UNSAT (property holds)" });
    let stats2 = solution2.statistics();
    println!("  Variables: {}, Clauses: {}", stats2.num_variables(), stats2.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms\n",
        stats2.translation_time(), stats2.solving_time(), stats2.total_time());

    // Test 3: run looplessPath for smaller scope (13 Time is too slow)
    println!("Test 3: Run looplessPath for 7 Time, 3 Process");
    println!("Formula: invariants && looplessPath\n");

    let formula3 = model.invariants().and(model.loopless_path());
    let bounds3 = model.bounds(3, 7)?;
    let solution3 = solver.solve(&formula3, &bounds3)?;

    println!("Result: {}", if solution3.is_sat() { "SAT (instance found)" } else { "UNSAT (no instance)" });
    let stats3 = solution3.statistics();
    println!("  Variables: {}, Clauses: {}", stats3.num_variables(), stats3.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats3.translation_time(), stats3.solving_time(), stats3.total_time());

    Ok(())
}
