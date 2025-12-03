//! Graph coloring problem
//!
//! Given a graph and k colors, determine if the graph is k-colorable.
//! (No two adjacent vertices can have the same color.)
//!
//! Following Java: kodkod.examples.csp.GraphColoring
//! Uses a simple hardcoded graph structure.

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

fn run() {
    // Define a simple graph: vertices [0, 1, 2, 3, 4]
    // Edges (adjacency list): 0-1, 1-2, 2-3, 3-4, 4-0 (a cycle)
    let edges = vec![
        (0, 1),
        (1, 0),
        (1, 2),
        (2, 1),
        (2, 3),
        (3, 2),
        (3, 4),
        (4, 3),
        (4, 0),
        (0, 4),
    ];

    // Test with different numbers of colors
    let test_cases = vec![
        (2, false), // A 5-cycle requires at least 3 colors
        (3, true),  // A 5-cycle is 3-colorable
        (4, true),  // Also 4-colorable
    ];

    for (num_colors, expected_sat) in test_cases {
        println!("=== Graph Coloring: {num_colors} colors ===\n");
        solve_graph_coloring(&edges, num_colors, expected_sat);
    }
}

fn main() {
    run()
}

fn solve_graph_coloring(edges: &[(usize, usize)], num_colors: usize, expected_sat: bool) {
    // Count unique vertices
    let mut max_vertex = 0;
    for (u, v) in edges {
        max_vertex = max_vertex.max(*u).max(*v);
    }
    let num_vertices = max_vertex + 1;

    // Create universe: vertices + colors
    let mut atoms = Vec::new();
    for i in 0..num_vertices {
        atoms.push(format!("v{}", i));
    }
    for i in 0..num_colors {
        atoms.push(format!("c{}", i));
    }

    let atom_refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(&atom_refs).unwrap();
    let factory = universe.factory();

    // Create relations
    let vertex = Relation::unary("Vertex");
    let color = Relation::unary("Color");
    let edges_rel = Relation::binary("edges");
    let coloring = Relation::binary("coloring"); // vertex -> color

    let mut bounds = Bounds::new(universe);

    // Vertex: first num_vertices atoms
    let vertex_tuples: Vec<Vec<&str>> = (0..num_vertices)
        .map(|i| vec![atom_refs[i]])
        .collect();
    let vertex_refs: Vec<&[&str]> = vertex_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound_exactly(&vertex, factory.tuple_set(&vertex_refs).unwrap())
        .unwrap();

    // Color: last num_colors atoms
    let color_start = num_vertices;
    let color_tuples: Vec<Vec<&str>> = (0..num_colors)
        .map(|i| vec![atom_refs[color_start + i]])
        .collect();
    let color_refs: Vec<&[&str]> = color_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound_exactly(&color, factory.tuple_set(&color_refs).unwrap())
        .unwrap();

    // Edges: exact graph structure
    let edge_tuples: Vec<Vec<&str>> = edges
        .iter()
        .map(|(u, v)| vec![atom_refs[*u], atom_refs[*v]])
        .collect();
    let edge_refs: Vec<&[&str]> = edge_tuples.iter().map(|e| e.as_slice()).collect();
    bounds
        .bound_exactly(&edges_rel, factory.tuple_set(&edge_refs).unwrap())
        .unwrap();

    // Coloring: vertex -> color (cartesian product)
    let mut coloring_tuples = Vec::new();
    for i in 0..num_vertices {
        for j in 0..num_colors {
            coloring_tuples.push(vec![atom_refs[i], atom_refs[num_vertices + j]]);
        }
    }
    let coloring_refs: Vec<&[&str]> = coloring_tuples.iter().map(|v| v.as_slice()).collect();
    bounds
        .bound(&coloring, factory.none(2), factory.tuple_set(&coloring_refs).unwrap())
        .unwrap();

    // Formula: all vertices must have exactly one color,
    // and adjacent vertices must have different colors
    let v = Variable::unary("v");
    let v_expr = Expression::from(v.clone());

    // v has exactly one color
    let v_color = v_expr.clone().join(Expression::from(coloring.clone()));
    let one_color = v_color.clone().one();

    // Adjacent vertices have different colors
    let v_neighbors = v_expr.join(Expression::from(edges_rel.clone()));
    let neighbor_colors = v_neighbors.join(Expression::from(coloring.clone()));
    let no_conflict = v_color.intersection(neighbor_colors).no();

    let formula = Formula::forall(
        Decls::from(Decl::one_of(v.clone(), Expression::from(vertex))),
        one_color.and(no_conflict),
    );

    let solver = Solver::new(Options::default());
    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            let is_sat = solution.is_sat();
            println!("Result: {}", if is_sat { "SAT" } else { "UNSAT" });
            println!(
                "Variables: {}, Clauses: {}",
                solution.statistics().num_variables(),
                solution.statistics().num_clauses()
            );

            if is_sat != expected_sat {
                eprintln!("ERROR: Expected {}, got {}", expected_sat, is_sat);
            } else {
                println!("✓ Result matches expectation");
            }
        }
        Err(e) => {
            eprintln!("Error: {:?}", e);
        }
    }
    println!();
}

#[test]
fn test_csp_graph_coloring_simple_runs() {
    // Test that the example runs without panicking
    run();
}
