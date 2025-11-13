use criterion::{black_box, criterion_group, criterion_main, Criterion};
use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

/// Pigeonhole-style problem: n+1 items must go into n slots
fn pigeonhole_problem(num_items: usize, num_slots: usize) -> (Formula, Bounds) {
    let item = Relation::unary("Item");
    let slot = Relation::unary("Slot");
    let assignment = Relation::binary("assignment"); // Item -> Slot

    // Build atoms as String vectors to avoid lifetime issues
    let item_atoms: Vec<String> = (0..num_items)
        .map(|i| format!("Item{}", i))
        .collect();
    let slot_atoms: Vec<String> = (0..num_slots)
        .map(|i| format!("Slot{}", i))
        .collect();

    // Create universe
    let all_atoms: Vec<String> = item_atoms.iter().chain(slot_atoms.iter()).cloned().collect();
    let atom_strs: Vec<&str> = all_atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(&atom_strs).unwrap();
    let factory = universe.factory();

    let mut bounds = Bounds::new(universe);

    // Item bounds
    let item_strs: Vec<&str> = item_atoms.iter().map(|s| s.as_str()).collect();
    let item_tuples: Vec<Vec<&str>> = item_strs.iter().map(|&s| vec![s]).collect();
    let item_refs: Vec<&[&str]> = item_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&item, factory.tuple_set(&item_refs).unwrap()).unwrap();

    // Slot bounds
    let slot_strs: Vec<&str> = slot_atoms.iter().map(|s| s.as_str()).collect();
    let slot_tuples: Vec<Vec<&str>> = slot_strs.iter().map(|&s| vec![s]).collect();
    let slot_refs: Vec<&[&str]> = slot_tuples.iter().map(|v| v.as_slice()).collect();
    bounds.bound_exactly(&slot, factory.tuple_set(&slot_refs).unwrap()).unwrap();

    // Assignment bounds: every item assigned to some slot
    let all_pairings = factory.all(2);
    bounds.bound(&assignment, factory.none(2), all_pairings).unwrap();

    // Formula: pigeonhole constraint
    let formula = Expression::from(item).some();

    (formula, bounds)
}

fn solver_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("solver");

    // Benchmark translation time for different problem sizes
    group.bench_function("pigeonhole_3x3", |b| {
        b.iter(|| {
            let (formula, bounds) = black_box(pigeonhole_problem(3, 3));
            let solver = Solver::new(Options::default());
            let _ = solver.solve(&formula, &bounds);
        });
    });

    group.bench_function("pigeonhole_4x3", |b| {
        b.iter(|| {
            let (formula, bounds) = black_box(pigeonhole_problem(4, 3));
            let solver = Solver::new(Options::default());
            let _ = solver.solve(&formula, &bounds);
        });
    });

    group.bench_function("pigeonhole_5x4", |b| {
        b.iter(|| {
            let (formula, bounds) = black_box(pigeonhole_problem(5, 4));
            let solver = Solver::new(Options::default());
            let _ = solver.solve(&formula, &bounds);
        });
    });

    group.finish();
}

criterion_group!(benches, solver_benchmarks);
criterion_main!(benches);
