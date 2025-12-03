//! Dijkstra's Mutual Exclusion Algorithm
//!
//! Models mutual exclusion with processes acquiring and releasing mutexes.
//! Based on kodkod.examples.alloy.Dijkstra

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable, RelationPredicate};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct Dijkstra {
    // Main relations
    process: Relation,
    mutex: Relation,
    state: Relation,
    holds: Relation,
    waits: Relation,

    // State ordering
    sfirst: Relation,
    slast: Relation,
    sord: Relation,

    // Mutex ordering
    mfirst: Relation,
    mlast: Relation,
    mord: Relation,
}

impl Dijkstra {
    fn new() -> Self {
        Self {
            process: Relation::unary("Process"),
            mutex: Relation::unary("Mutex"),
            state: Relation::unary("State"),
            holds: Relation::ternary("holds"),
            waits: Relation::ternary("waits"),
            sfirst: Relation::unary("sfirst"),
            slast: Relation::unary("slast"),
            sord: Relation::binary("sord"),
            mfirst: Relation::unary("mfirst"),
            mlast: Relation::unary("mlast"),
            mord: Relation::binary("mord"),
        }
    }

    /// Declaration constraints
    /// sig Process {}
    /// sig Mutex {}
    /// sig State { holds, waits: Process -> Mutex }
    fn declarations(&self) -> Formula {
        let f1 = Formula::RelationPredicate(RelationPredicate::TotalOrdering {
            relation: self.sord.clone(),
            ordered: self.state.clone(),
            first: self.sfirst.clone(),
            last: self.slast.clone(),
        });

        let f2 = Formula::RelationPredicate(RelationPredicate::TotalOrdering {
            relation: self.mord.clone(),
            ordered: self.mutex.clone(),
            first: self.mfirst.clone(),
            last: self.mlast.clone(),
        });

        let f3 = Expression::from(self.holds.clone())
            .in_set(Expression::from(self.state.clone())
                .product(Expression::from(self.process.clone()))
                .product(Expression::from(self.mutex.clone())));

        let f4 = Expression::from(self.waits.clone())
            .in_set(Expression::from(self.state.clone())
                .product(Expression::from(self.process.clone()))
                .product(Expression::from(self.mutex.clone())));

        Formula::and_all(vec![f1, f2, f3, f4])
    }

    /// pred State.Initial () { no this.holds + this.waits }
    fn initial(&self, s: Expression) -> Formula {
        s.clone().join(Expression::from(self.holds.clone()))
            .union(s.join(Expression::from(self.waits.clone())))
            .no()
    }

    /// pred State.IsFree (m: Mutex) {
    ///   no m.~(this.holds)
    /// }
    fn is_free(&self, s: Expression, m: Expression) -> Formula {
        m.join(s.join(Expression::from(self.holds.clone())).transpose()).no()
    }

    /// pred State.IsStalled (p: Process) { some p.(this.waits) }
    fn is_stalled(&self, s: Expression, p: Expression) -> Formula {
        p.join(s.join(Expression::from(self.waits.clone()))).some()
    }

    /// pred State.GrabMutex (p: Process, m: Mutex, s': State)
    fn grab_mutex(&self, s1: Expression, s2: Expression, p: Expression, m: Expression) -> Formula {
        let f1 = self.is_stalled(s1.clone(), p.clone()).not()
            .and(m.clone().in_set(p.clone().join(s1.clone().join(Expression::from(self.holds.clone())))).not());

        let is_free = self.is_free(s1.clone(), m.clone());

        let f2 = p.clone().join(s2.clone().join(Expression::from(self.holds.clone())))
            .equals(p.clone().join(s1.clone().join(Expression::from(self.holds.clone()))).union(m.clone()));

        let f3 = p.clone().join(s2.clone().join(Expression::from(self.waits.clone()))).no();
        let f4 = is_free.clone().implies(f2.and(f3));

        let f5 = p.clone().join(s2.clone().join(Expression::from(self.holds.clone())))
            .equals(p.clone().join(s1.clone().join(Expression::from(self.holds.clone()))));

        let f6 = p.clone().join(s2.clone().join(Expression::from(self.waits.clone())))
            .equals(m);

        let f7 = is_free.not().implies(f5.and(f6));

        let other_proc = Variable::unary("otherProc");
        let f8 = Expression::from(other_proc.clone()).join(s2.clone().join(Expression::from(self.holds.clone())))
            .equals(Expression::from(other_proc.clone()).join(s1.clone().join(Expression::from(self.holds.clone()))));

        let f9 = Expression::from(other_proc.clone()).join(s2.join(Expression::from(self.waits.clone())))
            .equals(Expression::from(other_proc.clone()).join(s1.join(Expression::from(self.waits.clone()))));

        let f10 = Formula::forall(
            Decls::from(Decl::one_of(other_proc, Expression::from(self.process.clone()).difference(p))),
            f8.and(f9)
        );

        Formula::and_all(vec![f1, f4, f7, f10])
    }

    /// pred State.ReleaseMutex (p: Process, m: Mutex, s': State)
    fn release_mutex(&self, s1: Expression, s2: Expression, p: Expression, m: Expression) -> Formula {
        let f1 = self.is_stalled(s1.clone(), p.clone()).not()
            .and(m.clone().in_set(p.clone().join(s1.clone().join(Expression::from(self.holds.clone())))));

        let f2 = p.clone().join(s2.clone().join(Expression::from(self.holds.clone())))
            .equals(p.clone().join(s1.clone().join(Expression::from(self.holds.clone()))).difference(m.clone()));

        let f3 = p.join(s2.clone().join(Expression::from(self.waits.clone()))).no();

        let cexpr = m.clone().join(s1.clone().join(Expression::from(self.waits.clone())).transpose());

        let f4 = m.clone().join(s2.clone().join(Expression::from(self.holds.clone())).transpose()).no();
        let f5 = m.clone().join(s2.clone().join(Expression::from(self.waits.clone())).transpose()).no();
        let f6 = cexpr.clone().no().implies(f4.and(f5));

        let lucky = Variable::unary("lucky");
        let f7 = m.clone().join(s2.clone().join(Expression::from(self.waits.clone())).transpose())
            .equals(m.clone().join(s1.clone().join(Expression::from(self.waits.clone())).transpose())
                .difference(Expression::from(lucky.clone())));

        let f8 = m.clone().join(s2.clone().join(Expression::from(self.holds.clone())).transpose())
            .equals(Expression::from(lucky.clone()));

        let f9 = Formula::exists(
            Decls::from(Decl::one_of(lucky, m.clone().join(s1.clone().join(Expression::from(self.waits.clone())).transpose()))),
            f7.and(f8)
        );

        let f10 = cexpr.some().implies(f9);

        let mu = Variable::unary("mu");
        let f11 = Expression::from(mu.clone()).join(s2.clone().join(Expression::from(self.waits.clone())).transpose())
            .equals(Expression::from(mu.clone()).join(s1.clone().join(Expression::from(self.waits.clone())).transpose()));

        let f12 = Expression::from(mu.clone()).join(s2.join(Expression::from(self.holds.clone())).transpose())
            .equals(Expression::from(mu.clone()).join(s1.join(Expression::from(self.holds.clone())).transpose()));

        let f13 = Formula::forall(
            Decls::from(Decl::one_of(mu, Expression::from(self.mutex.clone()).difference(m))),
            f11.and(f12)
        );

        Formula::and_all(vec![f1, f2, f3, f6, f10, f13])
    }

    /// pred GrabOrRelease ()
    fn grab_or_release(&self) -> Formula {
        let pre = Variable::unary("pre");
        let post = Expression::from(pre.clone()).join(Expression::from(self.sord.clone()));

        let f1 = post.clone().join(Expression::from(self.holds.clone()))
            .equals(Expression::from(pre.clone()).join(Expression::from(self.holds.clone())));

        let f2 = post.clone().join(Expression::from(self.waits.clone()))
            .equals(Expression::from(pre.clone()).join(Expression::from(self.waits.clone())));

        let p = Variable::unary("p");
        let m = Variable::unary("m");
        let d = Decls::from(Decl::one_of(p.clone(), Expression::from(self.process.clone())))
            .and(Decl::one_of(m.clone(), Expression::from(self.mutex.clone())));

        let f3 = Formula::exists(d.clone(),
            self.grab_mutex(Expression::from(pre.clone()), post.clone(), Expression::from(p.clone()), Expression::from(m.clone())));

        let f4 = Formula::exists(d,
            self.release_mutex(Expression::from(pre.clone()), post, Expression::from(p), Expression::from(m)));

        let all_body = f1.and(f2).or(f3).or(f4);

        self.initial(Expression::from(self.sfirst.clone()))
            .and(Formula::forall(
                Decls::from(Decl::one_of(pre, Expression::from(self.state.clone())
                    .difference(Expression::from(self.slast.clone())))),
                all_body
            ))
    }

    /// pred Deadlock () {
    ///   some s: State | all p: Process | some p.(s.waits)
    /// }
    fn deadlock(&self) -> Formula {
        let s = Variable::unary("s");
        let p = Variable::unary("p");

        Formula::exists(
            Decls::from(Decl::one_of(s.clone(), Expression::from(self.state.clone()))),
            Formula::forall(
                Decls::from(Decl::one_of(p.clone(), Expression::from(self.process.clone()))),
                Expression::from(p).join(Expression::from(s).join(Expression::from(self.waits.clone()))).some()
            )
        )
    }

    /// pred GrabbedInOrder ( ) {
    ///   all pre: State - so/last() |
    ///     let post = so/next(pre) |
    ///       let had = Process.(pre.holds), have = Process.(post.holds) |
    ///         let grabbed = have - had |
    ///           some grabbed => grabbed in mo/nexts(had)
    /// }
    fn grabbed_in_order(&self) -> Formula {
        let pre = Variable::unary("pre");
        let post = Expression::from(pre.clone()).join(Expression::from(self.sord.clone()));

        let had = Expression::from(self.process.clone())
            .join(Expression::from(pre.clone()).join(Expression::from(self.holds.clone())));

        let have = Expression::from(self.process.clone())
            .join(post.join(Expression::from(self.holds.clone())));

        let grabbed = have.difference(had.clone());

        Formula::forall(
            Decls::from(Decl::one_of(pre, Expression::from(self.state.clone())
                .difference(Expression::from(self.slast.clone())))),
            grabbed.clone().some().implies(
                grabbed.in_set(had.join(Expression::from(self.mord.clone()).closure()))
            )
        )
    }

    /// assert DijkstraPreventsDeadlocks {
    ///   some Process && GrabOrRelease() && GrabbedInOrder() => ! Deadlock()
    /// }
    fn check_dijkstra_prevents_deadlocks(&self) -> Formula {
        Formula::and_all(vec![
            self.declarations(),
            Expression::from(self.process.clone()).some(),
            self.grab_or_release(),
            self.grabbed_in_order(),
            self.deadlock()
        ])
    }

    /// Returns bounds for the given scope
    fn bounds(&self, states: usize, processes: usize, mutexes: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms = Vec::new();
        for i in 0..states {
            atoms.push(format!("State{}", i));
        }
        for i in 0..processes {
            atoms.push(format!("Process{}", i));
        }
        for i in 0..mutexes {
            atoms.push(format!("Mutex{}", i));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // State bounds
        let state_strs: Vec<String> = (0..states).map(|i| format!("State{}", i)).collect();
        let state_tuples: Vec<Vec<&str>> = state_strs.iter().map(|s| vec![s.as_str()]).collect();
        let state_refs: Vec<&[&str]> = state_tuples.iter().map(|v| v.as_slice()).collect();
        let state_bound = factory.tuple_set(&state_refs)?;

        // Process bounds
        let process_strs: Vec<String> = (0..processes).map(|i| format!("Process{}", i)).collect();
        let process_tuples: Vec<Vec<&str>> = process_strs.iter().map(|s| vec![s.as_str()]).collect();
        let process_refs: Vec<&[&str]> = process_tuples.iter().map(|v| v.as_slice()).collect();
        let process_bound = factory.tuple_set(&process_refs)?;

        // Mutex bounds
        let mutex_strs: Vec<String> = (0..mutexes).map(|i| format!("Mutex{}", i)).collect();
        let mutex_tuples: Vec<Vec<&str>> = mutex_strs.iter().map(|s| vec![s.as_str()]).collect();
        let mutex_refs: Vec<&[&str]> = mutex_tuples.iter().map(|v| v.as_slice()).collect();
        let mutex_bound = factory.tuple_set(&mutex_refs)?;

        bounds.bound_exactly(&self.state, state_bound.clone())?;
        bounds.bound(&self.holds, factory.none(3),
            state_bound.product(&process_bound)?.product(&mutex_bound)?)?;
        bounds.bound(&self.waits, factory.none(3),
            state_bound.product(&process_bound)?.product(&mutex_bound)?)?;

        bounds.bound(&self.sfirst, factory.none(1), state_bound.clone())?;
        bounds.bound(&self.slast, factory.none(1), state_bound.clone())?;
        bounds.bound(&self.sord, factory.none(2), state_bound.product(&state_bound)?)?;

        bounds.bound_exactly(&self.process, process_bound)?;

        bounds.bound_exactly(&self.mutex, mutex_bound.clone())?;
        bounds.bound(&self.mfirst, factory.none(1), mutex_bound.clone())?;
        bounds.bound(&self.mlast, factory.none(1), mutex_bound.clone())?;
        bounds.bound(&self.mord, factory.none(2), mutex_bound.product(&mutex_bound)?)?;

        Ok(bounds)
    }
}

fn run() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Dijkstra's Mutual Exclusion Algorithm ===\n");

    let model = Dijkstra::new();
    let options = Options::default();

    // Test: check DijkstraPreventsDeadlocks for 5 State, 3 Process, 3 Mutex
    println!("Test: Check DijkstraPreventsDeadlocks for 5 State, 3 Process, 3 Mutex");
    println!("Formula: declarations && some Process && GrabOrRelease && GrabbedInOrder && Deadlock\n");

    let formula = model.check_dijkstra_prevents_deadlocks();
    let bounds = model.bounds(5, 3, 3)?;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds)?;

    println!("Result: {}", if solution.is_sat() { "SAT (counterexample found - deadlock possible)" } else { "UNSAT (property holds - no deadlock)" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    run()
}

#[test]
fn test_alloy_dijkstra_runs() {
    run().unwrap();
}
