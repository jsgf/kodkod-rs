//! Lists - encoding of Alloy lists.als
//!
//! A KK encoding of lists with equivalence and prefix relations.
//!
//! Following Java: kodkod.examples.alloy.Lists

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct Lists {
    thing: Relation,
    list: Relation,
    non_empty_list: Relation,
    empty_list: Relation,
    car: Relation,
    cdr: Relation,
    equiv_to: Relation,
    prefixes: Relation,
}

impl Lists {
    fn new() -> Self {
        Self {
            thing: Relation::unary("Thing"),
            list: Relation::unary("List"),
            non_empty_list: Relation::unary("NonEmptyList"),
            empty_list: Relation::unary("EmptyList"),
            car: Relation::binary("car"),
            cdr: Relation::binary("cdr"),
            equiv_to: Relation::binary("equivTo"),
            prefixes: Relation::binary("prefixes"),
        }
    }

    /// Returns the declaration constraints
    fn decls(&self) -> Formula {
        // abstract sig List { equivTo: set List, prefixes: set List }
        // sig NonEmptyList extends List { car: one Thing, cdr: one List }
        // sig EmptyList extends List {}

        let f0 = Expression::from(self.list.clone())
            .equals(Expression::from(self.empty_list.clone())
                .union(Expression::from(self.non_empty_list.clone())));

        let f1 = Expression::from(self.empty_list.clone())
            .intersection(Expression::from(self.non_empty_list.clone()))
            .no();

        let f2 = Expression::from(self.equiv_to.clone())
            .in_set(Expression::from(self.list.clone())
                .product(Expression::from(self.list.clone())));

        let f3 = Expression::from(self.prefixes.clone())
            .in_set(Expression::from(self.list.clone())
                .product(Expression::from(self.list.clone())));

        let f4 = Formula::relation_predicate(
            kodkod_rs::ast::formula::RelationPredicate::function(
                self.car.clone(),
                Expression::from(self.non_empty_list.clone()),
                Expression::from(self.thing.clone())
            )
        );

        let f5 = Formula::relation_predicate(
            kodkod_rs::ast::formula::RelationPredicate::function(
                self.cdr.clone(),
                Expression::from(self.non_empty_list.clone()),
                Expression::from(self.list.clone())
            )
        );

        Formula::and(Formula::and(Formula::and(f0, f1), Formula::and(f2, f3)), Formula::and(f4, f5))
    }

    /// Returns all facts in the model
    fn facts(&self) -> Formula {
        // fact NoStrayThings {Thing in List.car}
        let f0 = Expression::from(self.thing.clone())
            .in_set(Expression::from(self.list.clone())
                .join(Expression::from(self.car.clone())));

        // fact finite {all L: List | isFinite(L)}
        let l = Variable::unary("L");
        let f1 = Formula::forall(
            Decls::from(Decl::one_of(l.clone(), Expression::from(self.list.clone()))),
            self.is_finite(Expression::from(l))
        );

        // fact Equivalence {
        //   all a,b: List | (a in b.equivTo) <=> (a.car = b.car and b.cdr in a.cdr.equivTo)
        // }
        let a = Variable::unary("a");
        let b = Variable::unary("b");

        let f2 = Expression::from(a.clone())
            .in_set(Expression::from(b.clone())
                .join(Expression::from(self.equiv_to.clone())));

        let f3 = Expression::from(a.clone())
            .join(Expression::from(self.car.clone()))
            .equals(Expression::from(b.clone())
                .join(Expression::from(self.car.clone())));

        let f4 = Expression::from(b.clone())
            .join(Expression::from(self.cdr.clone()))
            .in_set(Expression::from(a.clone())
                .join(Expression::from(self.cdr.clone()))
                .join(Expression::from(self.equiv_to.clone())));

        let f6 = Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::from(self.list.clone())))
                .and(Decl::one_of(b.clone(), Expression::from(self.list.clone()))),
            f2.iff(f3.clone().and(f4))
        );

        // fact prefix { //a is a prefix of b
        //   List->EmptyList in prefixes
        //   all a,b: NonEmptyList | (a in b.prefixes) <=> (a.car = b.car and a.cdr in b.cdr.prefixes)
        // }
        let f7 = Expression::from(self.list.clone())
            .product(Expression::from(self.empty_list.clone()))
            .in_set(Expression::from(self.prefixes.clone()));

        let f8 = Expression::from(a.clone())
            .in_set(Expression::from(b.clone())
                .join(Expression::from(self.prefixes.clone())));

        let f9 = Expression::from(a.clone())
            .join(Expression::from(self.cdr.clone()))
            .in_set(Expression::from(b.clone())
                .join(Expression::from(self.cdr.clone()))
                .join(Expression::from(self.prefixes.clone())));

        let f11 = Formula::forall(
            Decls::from(Decl::one_of(a, Expression::from(self.non_empty_list.clone())))
                .and(Decl::one_of(b, Expression::from(self.non_empty_list.clone()))),
            f8.iff(f3.clone().and(f9))
        );

        Formula::and(Formula::and(f0, f1), Formula::and(f6, Formula::and(f7, f11)))
    }

    /// Returns the isFinite predicate
    fn is_finite(&self, l: Expression) -> Formula {
        // pred isFinite (L:List) {some EmptyList & L.*cdr}
        Expression::from(self.empty_list.clone())
            .intersection(l.join(Expression::from(self.cdr.clone()).reflexive_closure()))
            .some()
    }

    /// Returns the reflexive assertion
    fn reflexive(&self) -> Formula {
        // assert reflexive {all L: List | L in L.equivTo}
        let l = Variable::unary("L");
        Formula::forall(
            Decls::from(Decl::one_of(l.clone(), Expression::from(self.list.clone()))),
            Expression::from(l.clone())
                .in_set(Expression::from(l).join(Expression::from(self.equiv_to.clone())))
        )
    }

    /// Returns the symmetric assertion
    fn symmetric(&self) -> Formula {
        // assert symmetric { ~equivTo in equivTo }
        Expression::from(self.equiv_to.clone())
            .transpose()
            .in_set(Expression::from(self.equiv_to.clone()))
    }

    /// Returns the empties assertion
    fn empties(&self) -> Formula {
        // assert empties { EmptyList->EmptyList in equivTo}
        Expression::from(self.empty_list.clone())
            .product(Expression::from(self.empty_list.clone()))
            .in_set(Expression::from(self.equiv_to.clone()))
    }

    /// Returns the show predicate
    fn show(&self) -> Formula {
        // pred show() {
        //   some disj a, b: NonEmptyList | b in a.prefixes
        // }
        let a = Variable::unary("a");
        let b = Variable::unary("b");

        Formula::exists(
            Decls::from(Decl::one_of(a.clone(), Expression::from(self.non_empty_list.clone())))
                .and(Decl::one_of(b.clone(), Expression::from(self.non_empty_list.clone()))),
            Expression::from(a.clone())
                .equals(Expression::from(b.clone()))
                .not()
                .and(Expression::from(b).in_set(
                    Expression::from(a).join(Expression::from(self.prefixes.clone()))
                ))
        )
    }

    /// Returns the conjunction of declaration constraints and facts
    fn invariants(&self) -> Formula {
        self.decls().and(self.facts())
    }

    /// Returns the conjunction of invariants and the show predicate
    fn run_show(&self) -> Formula {
        self.invariants().and(self.show())
    }

    /// Returns the conjunction of invariants and the negation of the empty hypothesis
    fn check_empties(&self) -> Formula {
        self.invariants().and(self.empties().not())
    }

    /// Returns the conjunction of invariants and the negation of the reflexive hypothesis
    fn check_reflexive(&self) -> Formula {
        self.invariants().and(self.reflexive().not())
    }

    /// Returns the conjunction of invariants and the negation of the symmetric hypothesis
    fn check_symmetric(&self) -> Formula {
        self.invariants().and(self.symmetric().not())
    }

    /// Returns the bounds for the given scope
    fn bounds(&self, scope: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(scope > 0);

        let mut atoms = Vec::new();
        for i in 0..scope {
            atoms.push(format!("Thing{}", i));
        }
        for i in 0..scope {
            atoms.push(format!("List{}", i));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        let max = scope - 1;

        let thing_bound = factory.range(
            factory.tuple(&["Thing0"])?,
            factory.tuple(&[&format!("Thing{}", max)])?
        )?;
        bounds.bound(&self.thing, factory.none(1), thing_bound.clone())?;

        let list_bound = factory.range(
            factory.tuple(&["List0"])?,
            factory.tuple(&[&format!("List{}", max)])?
        )?;
        bounds.bound(&self.list, factory.none(1), list_bound.clone())?;
        bounds.bound(&self.empty_list, factory.none(1), list_bound.clone())?;
        bounds.bound(&self.non_empty_list, factory.none(1), list_bound.clone())?;

        let car_bound = list_bound.product(&thing_bound)?;
        bounds.bound(&self.car, factory.none(2), car_bound)?;

        let cdr_bound = list_bound.product(&list_bound)?;
        bounds.bound(&self.cdr, factory.none(2), cdr_bound.clone())?;
        bounds.bound(&self.equiv_to, factory.none(2), cdr_bound.clone())?;
        bounds.bound(&self.prefixes, factory.none(2), cdr_bound)?;

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <scope>", args[0]);
        std::process::exit(1);
    }

    let scope: usize = args[1].parse()
        .expect("scope must be a positive integer");

    let model = Lists::new();
    let bounds = model.bounds(scope)?;
    let solver = Solver::new(Options::default());

    println!("=== Lists (scope={}) ===\n", scope);

    // running show
    println!("running show");
    let formula = model.run_show();
    let solution = solver.solve(&formula, &bounds)?;
    println!("{}", if solution.is_sat() { "SAT" } else { "UNSAT" });
    println!("  Variables: {}, Clauses: {}", solution.statistics().num_variables(), solution.statistics().num_clauses());

    // checking empties
    println!("\nchecking empties");
    let formula = model.check_empties();
    let solution = solver.solve(&formula, &bounds)?;
    println!("{}", if solution.is_sat() { "SAT (counterexample found)" } else { "UNSAT (assertion holds)" });
    println!("  Variables: {}, Clauses: {}", solution.statistics().num_variables(), solution.statistics().num_clauses());

    // checking reflexive
    println!("\nchecking reflexive");
    let formula = model.check_reflexive();
    let solution = solver.solve(&formula, &bounds)?;
    println!("{}", if solution.is_sat() { "SAT (counterexample found)" } else { "UNSAT (assertion holds)" });
    println!("  Variables: {}, Clauses: {}", solution.statistics().num_variables(), solution.statistics().num_clauses());

    // checking symmetric
    println!("\nchecking symmetric");
    let formula = model.check_symmetric();
    let solution = solver.solve(&formula, &bounds)?;
    println!("{}", if solution.is_sat() { "SAT (counterexample found)" } else { "UNSAT (assertion holds)" });
    println!("  Variables: {}, Clauses: {}", solution.statistics().num_variables(), solution.statistics().num_clauses());

    Ok(())
}


#[test]
fn test_lists_show() {
    let model = Lists::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.run_show();
    let solution = solver.solve(&formula, &bounds).expect("Failed to solve");
    assert!(solution.is_sat(), "Lists show should be SAT");
}

#[test]
fn test_lists_check_empties() {
    let model = Lists::new();
    let bounds = model.bounds(3).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_empties();
    let solution = solver.solve(&formula, &bounds).expect("Failed to solve");
    // UNSAT means the assertion holds (no counterexample)
    assert!(!solution.is_sat(), "Lists check_empties should be UNSAT (assertion holds)");
}
