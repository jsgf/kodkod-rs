//! ALG212 - Majority algebra with dist_long conjecture
//!
//! A KK encoding of ALG212+1.p from http://www.cs.miami.edu/~tptp/
//! Tests the dist_long conjecture for majority algebras.
//!
//! Following Java: kodkod.examples.tptp.ALG212

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct ALG212 {
    f: Relation, // 4-ary function f(x, y, z)
}

impl ALG212 {
    fn new() -> Self {
        Self {
            f: Relation::nary("f", 4),
        }
    }

    /// Returns the declarations.
    /// all x,y,z: univ | one f[x][y][z]
    fn decls(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let z = Variable::unary("z");

        // f[x][y][z] means z.join(y.join(x.join(f)))
        let f_xyz = Expression::from(z.clone())
            .join(Expression::from(y.clone())
                .join(Expression::from(x.clone())
                    .join(Expression::from(self.f.clone()))));

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::UNIV))
                .and(Decl::one_of(y, Expression::UNIV))
                .and(Decl::one_of(z, Expression::UNIV)),
            f_xyz.one()
        )
    }

    /// Returns the majority axiom.
    /// all x, y: A | f[x][x][y] = x
    fn majority(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");

        // f[x][x][y] = y.join(x.join(x.join(f)))
        let f_xxy = Expression::from(y.clone())
            .join(Expression::from(x.clone())
                .join(Expression::from(x.clone())
                    .join(Expression::from(self.f.clone()))));

        Formula::forall(
            Decls::from(Decl::one_of(x.clone(), Expression::UNIV))
                .and(Decl::one_of(y, Expression::UNIV)),
            f_xxy.equals(Expression::from(x))
        )
    }

    /// Returns the permute1 axiom.
    /// all x, y, z: A | f[x][y][z] = f[z][x][y]
    fn permute1(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let z = Variable::unary("z");

        let f_xyz = Expression::from(z.clone())
            .join(Expression::from(y.clone())
                .join(Expression::from(x.clone())
                    .join(Expression::from(self.f.clone()))));

        let f_zxy = Expression::from(y.clone())
            .join(Expression::from(x.clone())
                .join(Expression::from(z.clone())
                    .join(Expression::from(self.f.clone()))));

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::UNIV))
                .and(Decl::one_of(y, Expression::UNIV))
                .and(Decl::one_of(z, Expression::UNIV)),
            f_xyz.equals(f_zxy)
        )
    }

    /// Returns the permute2 axiom.
    /// all x, y, z: A | f[x][y][z] = f[x][z][y]
    fn permute2(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let z = Variable::unary("z");

        let f_xyz = Expression::from(z.clone())
            .join(Expression::from(y.clone())
                .join(Expression::from(x.clone())
                    .join(Expression::from(self.f.clone()))));

        let f_xzy = Expression::from(y.clone())
            .join(Expression::from(z.clone())
                .join(Expression::from(x.clone())
                    .join(Expression::from(self.f.clone()))));

        Formula::forall(
            Decls::from(Decl::one_of(x, Expression::UNIV))
                .and(Decl::one_of(y, Expression::UNIV))
                .and(Decl::one_of(z, Expression::UNIV)),
            f_xyz.equals(f_xzy)
        )
    }

    /// Returns the associativity axiom.
    /// all w, x, y, z: A | f[f[x][w][y]][w][z] = f[x][w][f[y][w][z]]
    fn associativity(&self) -> Formula {
        let w = Variable::unary("w");
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let z = Variable::unary("z");

        let f = Expression::from(self.f.clone());

        // f[x][w][y] = y.join(w.join(x.join(f)))
        let e0 = Expression::from(y.clone())
            .join(Expression::from(w.clone())
                .join(Expression::from(x.clone()).join(f.clone())));

        // f[f[x][w][y]][w][z] = z.join(w.join(e0.join(f)))
        let e1 = Expression::from(z.clone())
            .join(Expression::from(w.clone()).join(e0.join(f.clone())));

        // f[y][w][z] = z.join(w.join(y.join(f)))
        let e2 = Expression::from(z.clone())
            .join(Expression::from(w.clone())
                .join(Expression::from(y.clone()).join(f.clone())));

        // f[x][w][f[y][w][z]] = e2.join(w.join(x.join(f)))
        let e3 = e2.join(Expression::from(w.clone())
            .join(Expression::from(x.clone()).join(f)));

        Formula::forall(
            Decls::from(Decl::one_of(w, Expression::UNIV))
                .and(Decl::one_of(x, Expression::UNIV))
                .and(Decl::one_of(y, Expression::UNIV))
                .and(Decl::one_of(z, Expression::UNIV)),
            e1.equals(e3)
        )
    }

    /// Returns the conjunction of all axioms.
    fn axioms(&self) -> Formula {
        self.decls()
            .and(self.majority())
            .and(self.permute1())
            .and(self.permute2())
            .and(self.associativity())
    }

    /// Returns the dist_long conjecture.
    /// all u, w, x, y, z: A | f[f[x][y][z]][u][w] = f[f[x][u][w]][f[y][u][w]][f[z][u][w]]
    fn dist_long(&self) -> Formula {
        let u = Variable::unary("u");
        let w = Variable::unary("w");
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let z = Variable::unary("z");

        let f = Expression::from(self.f.clone());

        // f[x][y][z] = z.join(y.join(x.join(f)))
        let e0 = Expression::from(z.clone())
            .join(Expression::from(y.clone())
                .join(Expression::from(x.clone()).join(f.clone())));

        // f[f[x][y][z]][u][w] = w.join(u.join(e0.join(f)))
        let e1 = Expression::from(w.clone())
            .join(Expression::from(u.clone()).join(e0.join(f.clone())));

        // f[x][u][w] = w.join(u.join(x.join(f)))
        let e2 = Expression::from(w.clone())
            .join(Expression::from(u.clone())
                .join(Expression::from(x.clone()).join(f.clone())));

        // f[y][u][w] = w.join(u.join(y.join(f)))
        let e3 = Expression::from(w.clone())
            .join(Expression::from(u.clone())
                .join(Expression::from(y.clone()).join(f.clone())));

        // f[z][u][w] = w.join(u.join(z.join(f)))
        let e4 = Expression::from(w.clone())
            .join(Expression::from(u.clone())
                .join(Expression::from(z.clone()).join(f.clone())));

        // f[f[x][u][w]][f[y][u][w]][f[z][u][w]] = e4.join(e3.join(e2.join(f)))
        let e5 = e4.join(e3.join(e2.join(f)));

        Formula::forall(
            Decls::from(Decl::one_of(u, Expression::UNIV))
                .and(Decl::one_of(w, Expression::UNIV))
                .and(Decl::one_of(x, Expression::UNIV))
                .and(Decl::one_of(y, Expression::UNIV))
                .and(Decl::one_of(z, Expression::UNIV)),
            e1.equals(e5)
        )
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    fn check_dist_long(&self) -> Formula {
        self.axioms().and(self.dist_long().not())
    }

    /// Returns the bounds for the given scope.
    fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();

        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        b.bound(&self.f, f.none(4), f.all(4))?;

        Ok(b)
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_alg212 <univ_size>");
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

    let model = ALG212::new();
    let formula = model.check_dist_long();
    let bounds = model.bounds(n)?;

    println!("=== ALG212 (n={n}) ===\n");

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    println!("{}", if solution.is_sat() { "SAT (counterexample found)" } else { "UNSAT (conjecture holds)" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}

#[test]
fn test_alg212() {
    let model = ALG212::new();
    let formula = model.check_dist_long();
    let bounds = model.bounds(2).expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds).expect("Failed to solve");
    // UNSAT means the conjecture holds (no counterexample)
    assert!(!solution.is_sat(), "ALG212 check_dist_long should be UNSAT");
}
