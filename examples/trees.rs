//! Tree structure specification
//!
//! KK encoding of the Trees example from F. Zaraket, A. Aziz, and S. Khurshid's
//! "Sequential Encoding for Relational Analysis".
//!
//! Verifies five equivalent definitions of trees:
//! 1. Connected and acyclic
//! 2. Connected and removing any edge breaks connectivity
//! 3. Connected and |E| = |V| + |V| - 2
//! 4. Acyclic and |E| = |V| + |V| - 2
//! 5. Acyclic and adding any missing edge creates a cycle
//!
//! Following Java: kodkod.examples.alloy.Trees

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    let num_vertices = 3;  // Test with minimal size due to spec complexity
    println!(
        "=== Trees Specification (Tree Equivalence with {} vertices) ===\n",
        num_vertices
    );

    // Create universe with fixed size for simplicity
    let universe = match num_vertices {
        2 => Universe::new(&["v0", "v1"]).unwrap(),
        3 => Universe::new(&["v0", "v1", "v2"]).unwrap(),
        4 => Universe::new(&["v0", "v1", "v2", "v3"]).unwrap(),
        5 => Universe::new(&["v0", "v1", "v2", "v3", "v4"]).unwrap(),
        6 => Universe::new(&["v0", "v1", "v2", "v3", "v4", "v5"]).unwrap(),
        _ => panic!("Unsupported vertex count. Change source code for other sizes."),
    };

    let factory = universe.factory();

    // Create relations
    let v = Relation::unary("V");
    let e = Relation::binary("E");

    let mut bounds = Bounds::new(universe);

    // V = all atoms (exact bound)
    bounds
        .bound_exactly(&v, factory.all(1))
        .unwrap();

    // E: V x V (all possible edges)
    bounds
        .bound(&e, factory.none(2), factory.all(2))
        .unwrap();

    // Build specification: declarations, facts, and equivalence check
    let formula = build_spec(&v, &e);

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

fn build_spec(v: &Relation, e: &Relation) -> Formula {
    let mut specs = Vec::new();

    // Declarations and facts
    specs.push(decls_and_facts(v, e));

    // All 5 statements should be equivalent (cyclic implications)
    let s1 = statement1(v, e);
    let s2 = statement2(v, e);
    let s3 = statement3(v, e);
    let s4 = statement4(v, e);
    let s5 = statement5(v, e);

    // s1 => s2 => s3 => s4 => s5 => s1
    specs.push(s1.clone().implies(s2.clone()));
    specs.push(s2.clone().implies(s3.clone()));
    specs.push(s3.clone().implies(s4.clone()));
    specs.push(s4.clone().implies(s5.clone()));
    specs.push(s5.implies(s1));

    Formula::and_all(specs)
}

/// sig V { E: set V }
/// fact UndirectedGraph { E = ~E }
/// fact NonEmpty { some V }
fn decls_and_facts(v: &Relation, e: &Relation) -> Formula {
    let f0 = Expression::from(e.clone()).in_set(
        Expression::from(v.clone()).product(Expression::from(v.clone()))
    );
    let f1 = Expression::from(e.clone())
        .equals(Expression::from(e.clone()).transpose());
    let f2 = Expression::from(v.clone()).some();
    f0.and(f1).and(f2)
}

/// pred InCycle(v: V, c: V -> V) {
///   v in v.c or some v': v.c | v' in v.^(c - v->v' - v'->v')
/// }
fn in_cycle(v_expr: Expression, c: Expression) -> Formula {
    let v_prime = Variable::unary("v'");
    let v_expr_copy = v_expr.clone();
    let v_expr_copy2 = v_expr.clone();

    // v in v.c
    let f0 = v_expr.clone().in_set(v_expr_copy.clone().join(c.clone()));

    // some v': v.c | v' in v.^(c - v->v' - v'->v')
    let v_prime_expr = Expression::from(v_prime.clone());
    let c_copy = c.clone();
    let c_copy2 = c.clone();
    let edge_removed = c_copy
        .difference(v_expr_copy2.clone().product(v_prime_expr.clone()))
        .difference(v_prime_expr.clone().product(v_expr_copy2));
    let reachable = v_expr.join(edge_removed.closure());
    let f1 = v_prime_expr.in_set(reachable);

    f0.or(Formula::exists(
        Decls::from(Decl::one_of(&v_prime, &v_expr_copy.join(c_copy2))),
        f1,
    ))
}

/// pred Cyclic(c: V->V) { some v: V | inCycle(v, c) }
fn cyclic(v: &Relation, c: Expression) -> Formula {
    let v_var = Variable::unary("v");
    let v_var_expr = Expression::from(v_var.clone());
    let in_cycle_v = in_cycle(v_var_expr, c);

    Formula::exists(
        Decls::from(Decl::one_of(&v_var, &Expression::from(v.clone()))),
        in_cycle_v,
    )
}

/// pred Acyclic() { not Cyclic(E) }
fn acyclic(v: &Relation, e: Expression) -> Formula {
    cyclic(v, e).not()
}

/// pred Connected(c: V->V) { V x V in c* }
fn connected(v: &Relation, c: Expression) -> Formula {
    Expression::from(v.clone()).product(Expression::from(v.clone()))
        .in_set(c.reflexive_closure())
}

/// pred Statement1() { Connected(E) and Acyclic() }
fn statement1(v: &Relation, e: &Relation) -> Formula {
    let e_expr = Expression::from(e.clone());
    connected(v, e_expr.clone()).and(acyclic(v, e_expr))
}

/// pred Statement2() {
///   Connected(E) and
///   all u: V | all v: u.E | not Connected(E - (u->v) - (v->u))
/// }
fn statement2(v: &Relation, e: &Relation) -> Formula {
    let e_expr = Expression::from(e.clone());
    let u_var = Variable::unary("u");
    let v_var = Variable::unary("v");
    let u_expr = Expression::from(u_var.clone());
    let v_expr = Expression::from(v_var.clone());

    let connected_e = connected(v, e_expr.clone());
    let e_copy = e_expr.clone();
    let u_copy = u_expr.clone();
    let edge_removed = e_copy
        .difference(u_copy.clone().product(v_expr.clone()))
        .difference(v_expr.clone().product(u_copy));
    let f1 = connected(v, edge_removed).not();
    let f2 = Formula::forall(
        Decls::from(Decl::one_of(&v_var, &u_expr.join(e_expr))),
        f1,
    );
    let f3 = Formula::forall(
        Decls::from(Decl::one_of(&u_var, &Expression::from(v.clone()))),
        f2,
    );

    connected_e.and(f3)
}

/// pred Statement3() {
///   Connected(E) and #E = #V + #V - 2
/// }
fn statement3(v: &Relation, e: &Relation) -> Formula {
    let e_expr = Expression::from(e.clone());
    let v_count = Expression::from(v.clone()).count();
    let e_count = e_expr.clone().count();
    let expected = v_count.clone().plus(v_count).minus(
        kodkod_rs::ast::IntExpression::constant(2)
    );

    connected(v, e_expr).and(e_count.eq(expected))
}

/// pred Statement4() {
///   Acyclic() and #E = #V + #V - 2
/// }
fn statement4(v: &Relation, e: &Relation) -> Formula {
    let e_expr = Expression::from(e.clone());
    let v_count = Expression::from(v.clone()).count();
    let e_count = e_expr.clone().count();
    let expected = v_count.clone().plus(v_count).minus(
        kodkod_rs::ast::IntExpression::constant(2)
    );

    acyclic(v, e_expr).and(e_count.eq(expected))
}

/// pred Statement5() {
///   Acyclic() and
///   all u,v: V | (u->v) not in E implies Cyclic(E + (u->v) + (v->u))
/// }
fn statement5(v: &Relation, e: &Relation) -> Formula {
    let e_expr = Expression::from(e.clone());
    let u_var = Variable::unary("u");
    let v_var = Variable::unary("v");
    let u_expr = Expression::from(u_var.clone());
    let v_expr = Expression::from(v_var.clone());

    let u_copy = u_expr.clone();
    let v_copy = v_expr.clone();
    let edge_not_in = u_copy.product(v_copy.clone()).in_set(e_expr.clone()).not();
    let u_copy2 = u_expr.clone();
    let edge_added = e_expr.clone()
        .union(u_copy2.product(v_copy.clone()))
        .union(v_copy.product(u_expr.clone()));
    let f0 = edge_not_in.implies(cyclic(v, edge_added));

    let f1 = Formula::forall(
        Decls::from(Decl::one_of(&u_var, &Expression::from(v.clone())))
            .and(Decl::one_of(&v_var, &Expression::from(v.clone()))),
        f0,
    );

    acyclic(v, e_expr).and(f1)
}
