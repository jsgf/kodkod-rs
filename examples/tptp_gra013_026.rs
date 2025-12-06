//! GRA013_026 - Graph coloring Ramsey theory example
//!
//! A KK encoding of GRA019+1.p through GRA026+1.p from http://www.cs.miami.edu/~tptp/
//! Tests for colored cliques in graph coloring problems.
//!
//! Following Java: kodkod.examples.tptp.GRA013_026

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct GRA013_026 {
    pub node: Relation,
    pub red: Relation,
    pub green: Relation,
    pub less_than: Relation,
    pub goal: Relation,
    pub graph_size: usize,
    pub clique_size: usize,
}

impl GRA013_026 {
    pub fn new(graph_size: usize, clique_size: usize) -> Self {
        assert!(clique_size > 0, "cliqueSize must be positive");
        assert!(clique_size <= graph_size, "cliqueSize must be <= graph size");

        Self {
            node: Relation::unary("N"),
            red: Relation::binary("red"),
            green: Relation::binary("green"),
            less_than: Relation::binary("lessThan"),
            goal: Relation::unary("goal"),
            graph_size,
            clique_size,
        }
    }

    /// Creates a clique axiom for the given color.
    /// Generates variables V0..V(clique_size-1) where V(i+1) < V(i)
    /// and checks if all pairs are in the color relation.
    fn clique_axiom(&self, color: &Relation) -> Formula {
        // Create clique_size variables
        let vars: Vec<Variable> = (0..self.clique_size)
            .map(|i| Variable::unary(&format!("V{i}")))
            .collect();

        // Build the product of all pairs (V_i, V_j) where i < j
        // members = [V0 x (V1 + V2 + ...), V1 x (V2 + V3 + ...), ...]
        let mut members: Vec<Expression> = Vec::new();
        for i in 0..(self.clique_size - 1) {
            let rest: Vec<Expression> = vars[(i + 1)..self.clique_size]
                .iter()
                .map(|v| Expression::from(v.clone()))
                .collect();

            if !rest.is_empty() {
                let union_rest = rest.into_iter()
                    .reduce(|acc, e| acc.union(e))
                    .unwrap();
                members.push(Expression::from(vars[i].clone()).product(union_rest));
            }
        }

        let all_pairs = members.into_iter()
            .reduce(|acc, e| acc.union(e))
            .unwrap();

        // Build the decls: V0 in node, V1 in V0.lessThan, V2 in V1.lessThan, ...
        let mut decls = Decls::from(Decl::one_of(vars[0].clone(), Expression::from(self.node.clone())));
        for i in 1..self.clique_size {
            decls = decls.and(Decl::one_of(
                vars[i].clone(),
                Expression::from(vars[i - 1].clone()).join(Expression::from(self.less_than.clone()))
            ));
        }

        // all_pairs in color => goal.some
        let body = all_pairs.in_set(Expression::from(color.clone()))
            .implies(self.goal_to_be_proved());

        Formula::forall(decls, body)
    }

    /// Returns the red clique axiom.
    pub fn red_clique_axiom(&self) -> Formula {
        self.clique_axiom(&self.red)
    }

    /// Returns the green clique axiom.
    pub fn green_clique_axiom(&self) -> Formula {
        self.clique_axiom(&self.green)
    }

    /// Returns the partition axiom.
    /// lessThan in red + green
    pub fn partition(&self) -> Formula {
        Expression::from(self.less_than.clone())
            .in_set(
                Expression::from(self.red.clone())
                    .union(Expression::from(self.green.clone()))
            )
    }

    /// Returns the transitivity axiom.
    /// lessThan.lessThan in lessThan
    pub fn less_than_transitive(&self) -> Formula {
        Expression::from(self.less_than.clone())
            .join(Expression::from(self.less_than.clone()))
            .in_set(Expression::from(self.less_than.clone()))
    }

    /// Returns the no overlap axiom.
    /// no (red & green)
    pub fn no_overlap(&self) -> Formula {
        Expression::from(self.red.clone())
            .intersection(Expression::from(self.green.clone()))
            .no()
    }

    /// Returns the conjunction of all axioms.
    pub fn axioms(&self) -> Formula {
        self.red_clique_axiom()
            .and(self.green_clique_axiom())
            .and(self.partition())
            .and(self.less_than_transitive())
            .and(self.no_overlap())
    }

    /// Returns the goal_to_be_proved conjecture.
    pub fn goal_to_be_proved(&self) -> Formula {
        Expression::from(self.goal.clone()).some()
    }

    /// Returns the conjunction of the axioms and the negation of the hypothesis.
    pub fn check_goal_to_be_proved(&self) -> Formula {
        self.axioms().and(self.goal_to_be_proved().not())
    }

    /// Returns bounds for this problem.
    pub fn bounds(&self) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::with_capacity(self.graph_size + 1);
        for i in 1..=self.graph_size {
            atoms.push(format!("n{i}"));
        }
        atoms.push("goal".to_string());

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(&atom_strs)?;
        let f = u.factory();
        let mut b = Bounds::new(u);

        b.bound(&self.goal, f.none(1), f.set_of_atom("goal")?)?;

        let ns = f.range(f.tuple(&["n1"])?, f.tuple(&[&format!("n{}", self.graph_size)])?)?;
        b.bound_exactly(&self.node, ns.clone())?;

        // Build lessThan as a strict ordering on nodes
        let mut less_than_tuples = f.none(2);
        for i in 1..self.graph_size {
            for j in (i + 1)..self.graph_size {
                let t = f.tuple(&[&format!("n{i}"), &format!("n{j}")])?;
                less_than_tuples.add(t)?;
            }
        }
        b.bound_exactly(&self.less_than, less_than_tuples.clone())?;
        b.bound(&self.red, f.none(2), less_than_tuples.clone())?;
        b.bound(&self.green, f.none(2), less_than_tuples)?;

        Ok(b)
    }
}

fn usage() -> ! {
    eprintln!("Usage: tptp_gra013_026 <graph_size> <clique_size>");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        usage();
    }

    let graph_size: usize = args[1].parse().unwrap_or_else(|_| usage());
    let clique_size: usize = args[2].parse().unwrap_or_else(|_| usage());

    if graph_size < 1 || clique_size < 1 || clique_size > graph_size {
        usage();
    }

    let model = GRA013_026::new(graph_size, clique_size);
    let formula = model.check_goal_to_be_proved();
    let bounds = model.bounds()?;

    println!("=== GRA013_026 (graph_size={graph_size}, clique_size={clique_size}) ===\n");

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
fn test_gra013_026_runs() {
    let model = GRA013_026::new(5, 3);
    let bounds = model.bounds().expect("Failed to create bounds");
    let solver = Solver::new(Options::default());
    let formula = model.check_goal_to_be_proved();
    let _solution = solver.solve(&formula, &bounds).expect("Failed to solve");
}
