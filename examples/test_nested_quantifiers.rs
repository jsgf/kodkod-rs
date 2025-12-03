//! Test for nested quantifiers with same variable names

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    // Create a simple universe
    let universe = Universe::new(&["a", "b"]).unwrap();
    let factory = universe.factory();

    // Create relations
    let r1 = Relation::unary("R1");
    let r2 = Relation::binary("R2");

    let mut bounds = Bounds::new(universe);
    bounds.bound_exactly(&r1, factory.all(1)).unwrap();
    bounds.bound(&r2, factory.none(2), factory.all(2)).unwrap();

    // Create nested quantifiers: forall u in R1: forall v in u.R2: ...
    let u_var = Variable::unary("u");
    let v_var = Variable::unary("v");

    let u_expr = Expression::from(u_var.clone());
    let v_expr = Expression::from(v_var.clone());

    // Body: v in R1
    let body = v_expr.in_set(Expression::from(r1.clone()));

    // Inner forall: forall v in u.R2: v in R1
    let inner = Formula::forall(
        Decls::from(Decl::one_of(v_var, u_expr.join(Expression::from(r2.clone())))),
        body,
    );

    // Outer forall: forall u in R1: inner
    let formula = Formula::forall(
        Decls::from(Decl::one_of(u_var, Expression::from(r1.clone()))),
        inner,
    );

    let solver = Solver::new(Options::default());
    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            println!("Result: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
        }
        Err(e) => {
            eprintln!("Error: {:?}", e);
            std::process::exit(1);
        }
    }
}
