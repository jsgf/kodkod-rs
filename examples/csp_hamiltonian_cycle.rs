/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

//! Hamiltonian Cycle Problem
//!
//! Finds a Hamiltonian cycle in a graph (a cycle that visits each vertex exactly once).
//! Following Java: kodkod.examples.csp.HamiltonianCycle

use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::engine::evaluator::Evaluator;
use kodkod_rs::instance::{atom_as_str, Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solver};
use rand::Rng;

struct HamiltonianCycle {
    vertex: Relation,
    start: Relation,
    edges: Relation,
    cycle: Relation,
}

impl HamiltonianCycle {
    fn new() -> Self {
        Self {
            vertex: Relation::unary("Vertex"),
            start: Relation::unary("start"),
            edges: Relation::binary("edges"),
            cycle: Relation::binary("cycle"),
        }
    }

    /// Returns a formula that defines a Hamiltonian cycle
    fn cycle_definition(&self) -> Formula {
        // cycle is a function from vertices that have outgoing edges to vertices that have incoming edges
        let f0 = Formula::RelationPredicate(
            kodkod_rs::ast::RelationPredicate::Function {
                relation: self.cycle.clone(),
                domain: Expression::from(self.edges.clone()).join(Expression::from(self.vertex.clone())),
                range: Expression::from(self.vertex.clone()).join(Expression::from(self.edges.clone())),
            }
        );

        // All vertices are reachable from start via the cycle
        let f1 = Expression::from(self.vertex.clone()).in_set(
            Expression::from(self.start.clone()).join(Expression::from(self.cycle.clone()).closure())
        );

        f0.and(f1)
    }

    /// Generate a random graph with n vertices and approximately density fraction of possible edges
    fn random_graph_bounds(&self, n: usize, density: f64) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::new();
        for i in 0..n {
            atoms.push(format!("v{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        let all_vertices = factory.all(1);
        bounds.bound_exactly(&self.vertex, all_vertices.clone())?;
        bounds.bound_exactly(&self.start, factory.tuple_set(&[&["v0"]])?)?;

        // Generate random edges
        let mut rng = rand::thread_rng();
        let mut edge_tuples = factory.none(2);

        for i in 0..n {
            for j in 0..n {
                if i != j && rng.r#gen::<f64>() < density {
                    edge_tuples.add(factory.tuple(&[&format!("v{i}"), &format!("v{j}")])?)?;
                }
            }
        }

        bounds.bound_exactly(&self.edges, edge_tuples.clone())?;
        bounds.bound(&self.cycle, factory.none(2), edge_tuples)?;

        Ok(bounds)
    }

    /// Generate a complete graph (has Hamiltonian cycle)
    fn complete_graph_bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::new();
        for i in 0..n {
            atoms.push(format!("v{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        let all_vertices = factory.all(1);
        bounds.bound_exactly(&self.vertex, all_vertices)?;
        bounds.bound_exactly(&self.start, factory.tuple_set(&[&["v0"]])?)?;

        // Complete graph: edge from every vertex to every other vertex
        let mut edge_tuples = factory.none(2);
        for i in 0..n {
            for j in 0..n {
                if i != j {
                    edge_tuples.add(factory.tuple(&[&format!("v{i}"), &format!("v{j}")])?)?;
                }
            }
        }

        bounds.bound_exactly(&self.edges, edge_tuples.clone())?;
        bounds.bound(&self.cycle, factory.none(2), edge_tuples)?;

        Ok(bounds)
    }

    /// Print the cycle found in the solution
    fn print_cycle(&self, instance: &Instance) {
        let cycle_tuples = instance.tuples(&self.cycle).unwrap();
        let start_tuple = instance.tuples(&self.start).unwrap();

        if let Some(start_atom) = start_tuple.iter().next().and_then(|t| t.atom(0)) {
            let start_name = atom_as_str(start_atom).unwrap();
            print!("Cycle: {} ", start_name);

            let mut current = start_name;
            let mut visited = vec![current];

            loop {
                let mut found_next = false;
                for tuple in cycle_tuples.iter() {
                    if let (Some(from_atom), Some(to_atom)) = (tuple.atom(0), tuple.atom(1)) {
                        let from_name = atom_as_str(from_atom).unwrap();
                        let to_name = atom_as_str(to_atom).unwrap();

                        if from_name == current {
                            print!("-> {} ", to_name);
                            current = to_name;
                            visited.push(current);
                            found_next = true;
                            break;
                        }
                    }
                }

                if !found_next || current == start_name {
                    break;
                }

                if visited.len() > instance.tuples(&self.vertex).unwrap().size() + 1 {
                    println!("(cycle detection error)");
                    break;
                }
            }
            println!();
        }
    }

    /// Verify the solution is correct
    fn verify(&self, instance: &Instance) -> bool {
        let eval = Evaluator::new(instance);
        eval.evaluate(&self.cycle_definition())
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    let n = if args.len() > 1 {
        args[1].parse().unwrap_or(5)
    } else {
        5
    };

    let graph_type = if args.len() > 2 {
        &args[2]
    } else {
        "complete"
    };

    println!("=== Hamiltonian Cycle Problem ({n} vertices, {graph_type} graph) ===\n");

    let model = HamiltonianCycle::new();
    let formula = model.cycle_definition();

    let bounds = match graph_type {
        "complete" => model.complete_graph_bounds(n)?,
        "random" => model.random_graph_bounds(n, 0.5)?,
        _ => {
            eprintln!("Unknown graph type: {graph_type}. Use 'complete' or 'random'");
            return Ok(());
        }
    };

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    if solution.is_sat() {
        println!("Solution found!");
        model.print_cycle(solution.instance().unwrap());

        print!("Verifying solution... ");
        if model.verify(solution.instance().unwrap()) {
            println!("correct");
        } else {
            println!("incorrect!");
        }
    } else {
        println!("No Hamiltonian cycle exists");
    }

    let stats = solution.statistics();
    println!("\nStatistics:");
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}
