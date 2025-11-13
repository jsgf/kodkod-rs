use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use kodkod_rs::ast::{Expression, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Test multiple SAT solvers on the same problem
/// Currently uses batsat, but framework allows easy addition of other solvers
fn solver_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("solver_comparison");

    // Simple pigeonhole problem for comparing solvers
    for (num_pigeons, num_holes) in &[(3, 3), (4, 3), (5, 4)] {
        let problem_name = format!("pigeonhole_{}_{}", num_pigeons, num_holes);

        group.bench_with_input(
            BenchmarkId::from_parameter(&problem_name),
            &(*num_pigeons, *num_holes),
            |b, &(n_pigeons, n_holes)| {
                b.iter(|| {
                    let pigeon = Relation::unary("Pigeon");
                    let hole = Relation::unary("Hole");
                    let hole_rel = Relation::binary("hole");

                    // Build atoms
                    let pigeon_atoms: Vec<String> = (0..n_pigeons)
                        .map(|i| format!("Pigeon{}", i))
                        .collect();
                    let hole_atoms: Vec<String> = (0..n_holes)
                        .map(|i| format!("Hole{}", i))
                        .collect();

                    let all_atoms: Vec<String> = pigeon_atoms.iter().chain(hole_atoms.iter()).cloned().collect();
                    let atom_strs: Vec<&str> = all_atoms.iter().map(|s| s.as_str()).collect();
                    let universe = Universe::new(&atom_strs).unwrap();
                    let factory = universe.factory();

                    let mut bounds = Bounds::new(universe);

                    // Pigeons
                    let pigeon_strs: Vec<&str> = pigeon_atoms.iter().map(|s| s.as_str()).collect();
                    let pigeon_tuples: Vec<Vec<&str>> =
                        pigeon_strs.iter().map(|&s| vec![s]).collect();
                    let pigeon_refs: Vec<&[&str]> =
                        pigeon_tuples.iter().map(|v| v.as_slice()).collect();
                    bounds
                        .bound_exactly(&pigeon, factory.tuple_set(&pigeon_refs).unwrap())
                        .unwrap();

                    // Holes
                    let hole_strs: Vec<&str> = hole_atoms.iter().map(|s| s.as_str()).collect();
                    let hole_tuples: Vec<Vec<&str>> =
                        hole_strs.iter().map(|&s| vec![s]).collect();
                    let hole_refs: Vec<&[&str]> =
                        hole_tuples.iter().map(|v| v.as_slice()).collect();
                    bounds
                        .bound_exactly(&hole, factory.tuple_set(&hole_refs).unwrap())
                        .unwrap();

                    // hole_rel bounds: Pigeon x Hole
                    let all_binary = factory.all(2);
                    bounds
                        .bound(&hole_rel, factory.none(2), all_binary)
                        .unwrap();

                    // Simple formula: at least one pigeon
                    let formula = Expression::from(pigeon).some();

                    let solver = Solver::new(Options::default());
                    let _ = solver.solve(&formula, &bounds);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, solver_comparison);
criterion_main!(benches);
