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

//! Graph Coloring Problem
//!
//! Determines if a graph can be colored with k colors such that no adjacent vertices share a color.
//! Following Java: kodkod.examples.csp.GraphColoring

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::engine::evaluator::Evaluator;
use kodkod_rs::instance::{atom_as_str, Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solver};
use rand::Rng;

struct GraphColoring {
    vertex: Relation,
    color: Relation,
    edges: Relation,
    v2c: Relation, // vertex to color mapping
}

impl GraphColoring {
    fn new() -> Self {
        Self {
            vertex: Relation::unary("Vertex"),
            color: Relation::unary("Color"),
            edges: Relation::binary("edges"),
            v2c: Relation::binary("color"),
        }
    }

    /// Returns a formula stating that all vertices have one color,
    /// and that no two adjacent vertices have the same color
    fn coloring(&self) -> Formula {
        let v = Variable::unary("v");
        let vcolor = Expression::from(v.clone()).join(Expression::from(self.v2c.clone()));

        // Each vertex has exactly one color
        let f0 = vcolor.clone().one();

        // No adjacent vertices share a color
        let f1 = vcolor.intersection(
            Expression::from(v.clone())
                .join(Expression::from(self.edges.clone()))
                .join(Expression::from(self.v2c.clone()))
        ).no();

        Formula::forall(
            Decls::from(Decl::one_of(v, Expression::from(self.vertex.clone()))),
            f0.and(f1)
        )
    }

    /// Generate bounds for a random graph
    fn random_graph_bounds(&self, n_vertices: usize, k_colors: usize, density: f64) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::new();

        // Vertices
        for i in 0..n_vertices {
            atoms.push(format!("v{i}"));
        }

        // Colors
        for i in 0..k_colors {
            atoms.push(format!("c{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // Vertex bounds
        let vertex_tuples: Vec<Vec<&str>> = (0..n_vertices).map(|i| vec![&*atoms[i]]).collect();
        let vertex_refs: Vec<&[&str]> = vertex_tuples.iter().map(|v| v.as_slice()).collect();
        let vertex_set = factory.tuple_set(&vertex_refs)?;
        bounds.bound_exactly(&self.vertex, vertex_set.clone())?;

        // Color bounds
        let color_tuples: Vec<Vec<&str>> = (0..k_colors).map(|i| vec![&*atoms[n_vertices + i]]).collect();
        let color_refs: Vec<&[&str]> = color_tuples.iter().map(|v| v.as_slice()).collect();
        let color_set = factory.tuple_set(&color_refs)?;
        bounds.bound_exactly(&self.color, color_set.clone())?;

        // v2c bounds (vertex to color mapping)
        bounds.bound(&self.v2c, factory.none(2), vertex_set.product(&color_set)?)?;

        // Generate random edges
        let mut rng = rand::thread_rng();
        let mut edge_tuples = factory.none(2);
        for i in 0..n_vertices {
            for j in i + 1..n_vertices {
                if rng.r#gen::<f64>() < density {
                    edge_tuples.add(factory.tuple(&[&*atoms[i], &*atoms[j]])?)?;
                    edge_tuples.add(factory.tuple(&[&*atoms[j], &*atoms[i]])?)?;
                }
            }
        }
        bounds.bound_exactly(&self.edges, edge_tuples)?;

        Ok(bounds)
    }

    /// Generate bounds for a complete graph (requires n colors for n vertices)
    fn complete_graph_bounds(&self, n_vertices: usize, k_colors: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::new();

        // Vertices
        for i in 0..n_vertices {
            atoms.push(format!("v{i}"));
        }

        // Colors
        for i in 0..k_colors {
            atoms.push(format!("c{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // Vertex bounds
        let vertex_tuples: Vec<Vec<&str>> = (0..n_vertices).map(|i| vec![&*atoms[i]]).collect();
        let vertex_refs: Vec<&[&str]> = vertex_tuples.iter().map(|v| v.as_slice()).collect();
        let vertex_set = factory.tuple_set(&vertex_refs)?;
        bounds.bound_exactly(&self.vertex, vertex_set.clone())?;

        // Color bounds
        let color_tuples: Vec<Vec<&str>> = (0..k_colors).map(|i| vec![&*atoms[n_vertices + i]]).collect();
        let color_refs: Vec<&[&str]> = color_tuples.iter().map(|v| v.as_slice()).collect();
        let color_set = factory.tuple_set(&color_refs)?;
        bounds.bound_exactly(&self.color, color_set.clone())?;

        // v2c bounds
        bounds.bound(&self.v2c, factory.none(2), vertex_set.product(&color_set)?)?;

        // Complete graph edges
        let mut edge_tuples = factory.none(2);
        for i in 0..n_vertices {
            for j in 0..n_vertices {
                if i != j {
                    edge_tuples.add(factory.tuple(&[&*atoms[i], &*atoms[j]])?)?;
                }
            }
        }
        bounds.bound_exactly(&self.edges, edge_tuples)?;

        Ok(bounds)
    }

    /// Generate bounds for a cycle graph (requires 2 or 3 colors depending on odd/even)
    fn cycle_graph_bounds(&self, n_vertices: usize, k_colors: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms: Vec<String> = Vec::new();

        // Vertices
        for i in 0..n_vertices {
            atoms.push(format!("v{i}"));
        }

        // Colors
        for i in 0..k_colors {
            atoms.push(format!("c{i}"));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // Vertex bounds
        let vertex_tuples: Vec<Vec<&str>> = (0..n_vertices).map(|i| vec![&*atoms[i]]).collect();
        let vertex_refs: Vec<&[&str]> = vertex_tuples.iter().map(|v| v.as_slice()).collect();
        let vertex_set = factory.tuple_set(&vertex_refs)?;
        bounds.bound_exactly(&self.vertex, vertex_set.clone())?;

        // Color bounds
        let color_tuples: Vec<Vec<&str>> = (0..k_colors).map(|i| vec![&*atoms[n_vertices + i]]).collect();
        let color_refs: Vec<&[&str]> = color_tuples.iter().map(|v| v.as_slice()).collect();
        let color_set = factory.tuple_set(&color_refs)?;
        bounds.bound_exactly(&self.color, color_set.clone())?;

        // v2c bounds
        bounds.bound(&self.v2c, factory.none(2), vertex_set.product(&color_set)?)?;

        // Cycle edges
        let mut edge_tuples = factory.none(2);
        for i in 0..n_vertices {
            let next = (i + 1) % n_vertices;
            edge_tuples.add(factory.tuple(&[&*atoms[i], &*atoms[next]])?)?;
            edge_tuples.add(factory.tuple(&[&*atoms[next], &*atoms[i]])?)?;
        }
        bounds.bound_exactly(&self.edges, edge_tuples)?;

        Ok(bounds)
    }

    /// Print the coloring solution
    fn print_coloring(&self, instance: &Instance) {
        let v2c_tuples = instance.tuples(&self.v2c).unwrap();
        let vertex_tuples = instance.tuples(&self.vertex).unwrap();

        println!("Coloring:");
        for vertex_tuple in vertex_tuples.iter() {
            if let Some(v_atom) = vertex_tuple.atom(0) {
                let v_name = atom_as_str(v_atom).unwrap();

                // Find color for this vertex
                for color_tuple in v2c_tuples.iter() {
                    if let (Some(cv_atom), Some(c_atom)) = (color_tuple.atom(0), color_tuple.atom(1)) {
                        let cv_name = atom_as_str(cv_atom).unwrap();
                        let c_name = atom_as_str(c_atom).unwrap();

                        if cv_name == v_name {
                            println!("  {v_name} -> {c_name}");
                            break;
                        }
                    }
                }
            }
        }
    }

    /// Verify the coloring is correct
    fn verify(&self, instance: &Instance) -> bool {
        let eval = Evaluator::new(instance);
        eval.evaluate(&self.coloring())
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    let n_vertices = if args.len() > 1 {
        args[1].parse().unwrap_or(5)
    } else {
        5
    };

    let k_colors = if args.len() > 2 {
        args[2].parse().unwrap_or(3)
    } else {
        3
    };

    let graph_type = if args.len() > 3 {
        &args[3]
    } else {
        "random"
    };

    println!("=== Graph Coloring Problem ({n_vertices} vertices, {k_colors} colors, {graph_type} graph) ===\n");

    let model = GraphColoring::new();
    let formula = model.coloring();

    let bounds = match graph_type {
        "complete" => model.complete_graph_bounds(n_vertices, k_colors)?,
        "cycle" => model.cycle_graph_bounds(n_vertices, k_colors)?,
        "random" => model.random_graph_bounds(n_vertices, k_colors, 0.3)?,
        _ => {
            eprintln!("Unknown graph type: {graph_type}. Use 'complete', 'cycle', or 'random'");
            return Ok(());
        }
    };

    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    if solution.is_sat() {
        println!("Graph is {k_colors}-colorable!");
        model.print_coloring(solution.instance().unwrap());

        print!("\nVerifying solution... ");
        if model.verify(solution.instance().unwrap()) {
            println!("correct");
        } else {
            println!("incorrect!");
        }
    } else {
        println!("Graph is NOT {k_colors}-colorable");
    }

    let stats = solution.statistics();
    println!("\nStatistics:");
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}
