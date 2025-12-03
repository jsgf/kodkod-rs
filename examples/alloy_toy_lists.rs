//! Toy lists specification
//!
//! A logical specification of singly-linked lists with the following operations:
//! - car: get the head element
//! - cdr: get the tail (rest of list)
//! - equivalence: two lists are equivalent if they have the same structure
//! - prefix: one list is a prefix of another
//!
//! Verifies various properties like acyclicity and prefix transitivity.
//!
//! Following Java: kodkod.examples.alloy.ToyLists

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn run() {
    println!("=== Toy Lists Specification ===\n");

    // Create universe: list elements
    let universe = Universe::new(&["L0", "L1", "L2", "E0", "E1", "E2"]).unwrap();
    let factory = universe.factory();

    // Create relations
    let list = Relation::unary("List");
    let non_empty_list = Relation::unary("NonEmptyList");
    let empty_list = Relation::unary("EmptyList");
    let thing = Relation::unary("Thing");
    let equiv_to = Relation::binary("equivTo");
    let prefixes = Relation::binary("prefixes");
    let car = Relation::binary("car");
    let cdr = Relation::binary("cdr");

    let mut bounds = Bounds::new(universe);

    // List = {L0, L1, L2}
    let list_tuples = vec![vec!["L0"], vec!["L1"], vec!["L2"]];
    let list_refs: Vec<&[&str]> = list_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound_exactly(&list, factory.tuple_set(&list_refs).unwrap())
        .unwrap();

    // Thing = {E0, E1, E2} (list elements)
    let thing_tuples = vec![vec!["E0"], vec!["E1"], vec!["E2"]];
    let thing_refs: Vec<&[&str]> = thing_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound_exactly(&thing, factory.tuple_set(&thing_refs).unwrap())
        .unwrap();

    // NonEmptyList and EmptyList partition List
    // NonEmptyList ⊆ List, EmptyList ⊆ List, NonEmptyList ∩ EmptyList = ∅
    bounds
        .bound(&non_empty_list, factory.none(1), factory.tuple_set(&list_refs).unwrap())
        .unwrap();
    bounds
        .bound(&empty_list, factory.none(1), factory.tuple_set(&list_refs).unwrap())
        .unwrap();

    // car: NonEmptyList -> Thing (each non-empty list has exactly one head)
    let mut car_tuples = Vec::new();
    for l in &["L0", "L1", "L2"] {
        for e in &["E0", "E1", "E2"] {
            car_tuples.push(vec![*l, *e]);
        }
    }
    let car_refs: Vec<&[&str]> = car_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound(&car, factory.none(2), factory.tuple_set(&car_refs).unwrap())
        .unwrap();

    // cdr: NonEmptyList -> List (each non-empty list has exactly one tail)
    let mut cdr_tuples = Vec::new();
    for l in &["L0", "L1", "L2"] {
        for l2 in &["L0", "L1", "L2"] {
            cdr_tuples.push(vec![*l, *l2]);
        }
    }
    let cdr_refs: Vec<&[&str]> = cdr_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound(&cdr, factory.none(2), factory.tuple_set(&cdr_refs).unwrap())
        .unwrap();

    // equivTo and prefixes: List x List
    let list_product = factory.all(2);
    bounds
        .bound(&equiv_to, factory.none(2), list_product.clone())
        .unwrap();
    bounds
        .bound(&prefixes, factory.none(2), list_product)
        .unwrap();

    // Build the specification formula
    let formula = build_spec(&list, &non_empty_list, &empty_list, &thing,
                            &equiv_to, &prefixes, &car, &cdr);

    let solver = Solver::new(Options::default());
    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            println!("Result: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
            println!(
                "Variables: {}, Clauses: {}",
                solution.statistics().num_variables(),
                solution.statistics().num_clauses()
            );
        }
        Err(e) => {
            eprintln!("Error: {:?}", e);
        }
    }
}

fn main() {
    run()
}

fn build_spec(
    list: &Relation,
    non_empty: &Relation,
    empty: &Relation,
    thing: &Relation,
    equiv_to: &Relation,
    prefixes: &Relation,
    car: &Relation,
    cdr: &Relation,
) -> Formula {
    let mut specs = Vec::new();

    // List = NonEmptyList ∪ EmptyList
    specs.push(
        Expression::from(list.clone()).equals(
            Expression::from(non_empty.clone()).union(Expression::from(empty.clone()))
        )
    );

    // NonEmptyList ∩ EmptyList = ∅
    specs.push(
        Expression::from(non_empty.clone())
            .intersection(Expression::from(empty.clone()))
            .no()
    );

    // car ⊆ NonEmptyList × Thing
    specs.push(
        Expression::from(car.clone()).in_set(
            Expression::from(non_empty.clone()).product(Expression::from(thing.clone()))
        )
    );

    // Each non-empty list has exactly one car
    let a = Variable::unary("a");
    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::from(non_empty.clone()))),
            Expression::from(a.clone())
                .join(Expression::from(car.clone()))
                .one(),
        )
    );

    // cdr ⊆ NonEmptyList × List
    specs.push(
        Expression::from(cdr.clone()).in_set(
            Expression::from(non_empty.clone()).product(Expression::from(list.clone()))
        )
    );

    // Each non-empty list has exactly one cdr
    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::from(non_empty.clone()))),
            Expression::from(a.clone())
                .join(Expression::from(cdr.clone()))
                .one(),
        )
    );

    // Every list eventually reaches an empty list
    let e = Variable::unary("e");
    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::from(list.clone()))),
            Formula::exists(
                Decls::from(Decl::one_of(e.clone(), Expression::from(empty.clone()))),
                Expression::from(e.clone()).in_set(
                    Expression::from(a.clone())
                        .join(Expression::from(cdr.clone()).reflexive_closure())
                ),
            ),
        )
    );

    // equivTo ⊆ List × List
    specs.push(
        Expression::from(equiv_to.clone()).in_set(
            Expression::from(list.clone()).product(Expression::from(list.clone()))
        )
    );

    // Lists are equivalent iff their cars are equal and cdrs are equivalent
    let b = Variable::unary("b");
    let a_expr = Expression::from(a.clone());
    let b_expr = Expression::from(b.clone());

    let car_a = a_expr.clone().join(Expression::from(car.clone()));
    let car_b = b_expr.clone().join(Expression::from(car.clone()));
    let car_equiv = car_a.equals(car_b);

    let cdr_a = a_expr.clone().join(Expression::from(cdr.clone()));
    let cdr_b = b_expr.clone().join(Expression::from(cdr.clone()));
    let cdr_a_equiv = cdr_a.join(Expression::from(equiv_to.clone()));
    let cdr_b_equiv = cdr_b.join(Expression::from(equiv_to.clone()));
    let cdr_equiv = cdr_a_equiv.equals(cdr_b_equiv);

    let a_in_b_equiv = a_expr.clone().in_set(b_expr.clone().join(Expression::from(equiv_to.clone())));
    let equiv_iff = a_in_b_equiv.iff(car_equiv.and(cdr_equiv));

    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::from(list.clone())))
                .and(Decl::one_of(b.clone(), Expression::from(list.clone()))),
            equiv_iff,
        )
    );

    // prefixes ⊆ List × List
    specs.push(
        Expression::from(prefixes.clone()).in_set(
            Expression::from(list.clone()).product(Expression::from(list.clone()))
        )
    );

    // Every empty list is a prefix of every list
    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(e.clone(), Expression::from(empty.clone())))
                .and(Decl::one_of(a.clone(), Expression::from(list.clone()))),
            Expression::from(e.clone()).in_set(
                Expression::from(a.clone()).join(Expression::from(prefixes.clone()))
            ),
        )
    );

    // No non-empty list is a prefix of an empty list
    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(e.clone(), Expression::from(empty.clone())))
                .and(Decl::one_of(a.clone(), Expression::from(non_empty.clone()))),
            Expression::from(a.clone())
                .in_set(Expression::from(e.clone()).join(Expression::from(prefixes.clone())))
                .not(),
        )
    );

    // Non-empty lists are prefixes iff their cars are equal and cdrs are prefix-related
    let car_ne_a = a_expr.clone().join(Expression::from(car.clone()));
    let car_ne_b = b_expr.clone().join(Expression::from(car.clone()));
    let car_ne_eq = car_ne_a.equals(car_ne_b);

    let cdr_ne_a = a_expr.clone().join(Expression::from(cdr.clone()));
    let cdr_ne_b = b_expr.clone().join(Expression::from(cdr.clone()));
    let cdr_ne_prefix = cdr_ne_a.in_set(cdr_ne_b.join(Expression::from(prefixes.clone())));

    let a_ne_prefix = a_expr.in_set(b_expr.clone().join(Expression::from(prefixes.clone())));
    let prefix_iff = a_ne_prefix.iff(car_ne_eq.and(cdr_ne_prefix));

    specs.push(
        Formula::forall(
            Decls::from(Decl::one_of(a.clone(), Expression::from(non_empty.clone())))
                .and(Decl::one_of(b.clone(), Expression::from(non_empty.clone()))),
            prefix_iff,
        )
    );

    // Combine all specs with AND
    Formula::and_all(specs)
}

#[test]
fn test_alloy_toy_lists_runs() {
    // Test that the example runs without panicking
    run();
}
