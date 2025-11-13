//! Hotel security example (simplified)
//!
//! Models a hotel lock system with key cards, guests, and check-in/out events.
//! This is a simplified version of the Kodkod Hotel example focusing on core
//! constraint logic. We test the noBadEntry property which states that a guest
//! can only enter a room if they hold a valid key for it.
//!
//! Full specification requires Alloy predicates (total_order, function) that
//! aren't in core relational logic. This version focuses on the room access
//! constraint which is the critical safety property.

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    let scope = 2;
    println!("=== Hotel Example (scope: {}) ===\n", scope);

    // Relations
    let room = Relation::unary("Room");
    let guest = Relation::unary("Guest");
    let card = Relation::unary("Card");

    // holds[g,c] = true if guest g holds card c
    let holds = Relation::binary("holds");
    // room_key[r,c] = true if card c opens room r
    let room_key = Relation::binary("room_key");
    // guest_in_room[r,g] = true if guest g is currently in room r
    let guest_in = Relation::binary("guest_in");

    // Create universe
    let mut atoms = Vec::new();
    for i in 0..scope {
        atoms.push(format!("R{}", i));
    }
    for i in 0..scope {
        atoms.push(format!("G{}", i));
    }
    for i in 0..scope {
        atoms.push(format!("C{}", i));
    }

    let atom_refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(&atom_refs).unwrap();
    let factory = universe.factory();
    let mut bounds = Bounds::new(universe);

    // Bind Room, Guest, Card to their atoms
    let room_tuples: Vec<&[&str]> = (0..scope)
        .map(|i| std::slice::from_ref(&atom_refs[i]))
        .collect();
    let guest_tuples: Vec<&[&str]> = (scope..2 * scope)
        .map(|i| std::slice::from_ref(&atom_refs[i]))
        .collect();
    let card_tuples: Vec<&[&str]> = (2 * scope..3 * scope)
        .map(|i| std::slice::from_ref(&atom_refs[i]))
        .collect();

    bounds
        .bound_exactly(&room, factory.tuple_set(&room_tuples).unwrap())
        .unwrap();
    bounds
        .bound_exactly(&guest, factory.tuple_set(&guest_tuples).unwrap())
        .unwrap();
    bounds
        .bound_exactly(&card, factory.tuple_set(&card_tuples).unwrap())
        .unwrap();

    // holds: Guest × Card (any guest can hold any card)
    bounds
        .bound(&holds, factory.none(2), factory.all(2))
        .unwrap();

    // room_key: Room × Card (any card can open any room)
    bounds
        .bound(&room_key, factory.none(2), factory.all(2))
        .unwrap();

    // guest_in: Room × Guest (any guest can be in any room)
    bounds
        .bound(&guest_in, factory.none(2), factory.all(2))
        .unwrap();

    // Invariant: no_bad_entry
    // For all guests g and rooms r: if g is in r, then g must hold a card that opens r
    // ∀ r,g: (r,g) ∈ guest_in ⇒ ∃ c: (g,c) ∈ holds ∧ (r,c) ∈ room_key
    let r = Variable::unary("r");
    let g = Variable::unary("g");
    let c = Variable::unary("c");

    let r_expr = Expression::from(r.clone());
    let g_expr = Expression::from(g.clone());
    let c_expr = Expression::from(c.clone());

    // Build the constraint
    let has_card_for_room = c_expr
        .clone()
        .in_set(
            g_expr
                .clone()
                .join(Expression::from(&holds))
                .intersection(r_expr.clone().join(Expression::from(&room_key))),
        );

    let entry_ok = Formula::exists(
        Decls::from(Decl::one_of(c.clone(), Expression::from(&card))),
        has_card_for_room,
    );

    let guest_in_room_implies_has_key = Formula::forall(
        Decls::from(Decl::one_of(r.clone(), Expression::from(&room)))
            .and(Decl::one_of(g.clone(), Expression::from(&guest))),
        entry_ok,
    );

    // The formula we're checking: make sure no_bad_entry holds
    // We want this to be satisfiable (SAT)
    let formula = guest_in_room_implies_has_key;

    let solver = Solver::new(Options::default());
    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            println!("Result: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
            println!(
                "Variables: {}, Clauses: {}",
                solution.statistics().num_variables(),
                solution.statistics().num_clauses()
            );

            if solution.is_sat() {
                println!("\nConstraint is satisfiable - the system found a valid configuration");
                println!("where no guest enters a room without a valid key card.");
            }
        }
        Err(e) => {
            eprintln!("Error: {:?}", e);
        }
    }
}
