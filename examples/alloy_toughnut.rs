//! Toughnut - John McCarthy's domino covering problem
//!
//! Can you cover a chessboard with dominoes when opposite corners are removed?
//! Based on kodkod.examples.alloy.Toughnut

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct Toughnut {
    cell: Relation,
    covered: Relation,
    ord: Relation,
}

impl Toughnut {
    fn new() -> Self {
        Self {
            cell: Relation::unary("Cell"),
            covered: Relation::nary("covered", 4),
            ord: Relation::binary("ord"),
        }
    }

    fn next(&self, e: Expression) -> Expression {
        e.join(Expression::from(self.ord.clone()))
    }

    fn prev(&self, e: Expression) -> Expression {
        Expression::from(self.ord.clone()).join(e)
    }

    /// Returns the covering predicate
    fn check_below_too_double_prime(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let d = Decls::from(Decl::one_of(x.clone(), Expression::from(self.cell.clone())))
            .and(Decl::one_of(y.clone(), Expression::from(self.cell.clone())));

        let xy = Expression::from(y.clone())
            .join(Expression::from(x.clone()).join(Expression::from(self.covered.clone())));

        eprintln!("DEBUG: Building symm formula");
        // Covering relation is symmetric
        let symm = Formula::forall(d.clone(),
            xy.clone().product(Expression::from(x.clone()).product(Expression::from(y.clone())))
                .in_set(Expression::from(self.covered.clone()))
        );

        eprintln!("DEBUG: Building covering formula");
        // Each pair of cells on the board should be covered
        // by a domino, which also covers ONE of its neighbors
        let x_neighbors = self.prev(Expression::from(x.clone()))
            .union(self.next(Expression::from(x.clone())))
            .product(Expression::from(y.clone()));

        let y_neighbors = Expression::from(x.clone())
            .product(self.prev(Expression::from(y.clone()))
                .union(self.next(Expression::from(y.clone()))));

        let covering = Formula::forall(d,
            xy.clone().one().and(xy.in_set(x_neighbors.union(y_neighbors)))
        );

        eprintln!("DEBUG: Combining symm and covering");
        symm.and(covering)
    }

    /// Returns bounds for an n×n board
    fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(n > 0);

        let atoms: Vec<String> = (0..n).map(|i| i.to_string()).collect();
        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        // All cells
        let all_cells = factory.all(1);
        bounds.bound_exactly(&self.cell, all_cells)?;

        // Ordering: linear chain 0→1→2→...→n-1
        let mut ord_tuples = Vec::new();
        for i in 0..n-1 {
            ord_tuples.push(vec![i.to_string(), (i+1).to_string()]);
        }
        let ord_refs: Vec<Vec<&str>> = ord_tuples.iter()
            .map(|v| v.iter().map(|s| s.as_str()).collect())
            .collect();
        let ord_tuple_refs: Vec<&[&str]> = ord_refs.iter().map(|v| v.as_slice()).collect();
        let ord_bound = factory.tuple_set(&ord_tuple_refs)?;
        bounds.bound_exactly(&self.ord, ord_bound)?;

        // Board: all pairs except opposite corners (0,0) and (n-1,n-1)
        let mut board = factory.all(2);

        // Remove (0,0)
        let corner1 = factory.tuple(&["0", "0"])?;
        board.remove(&corner1);

        // Remove (n-1,n-1)
        let last = (n-1).to_string();
        let corner2 = factory.tuple(&[last.as_str(), last.as_str()])?;
        board.remove(&corner2);

        // Covered relation: board × board
        let covered_bound = board.product(&board)?;
        bounds.bound(&self.covered, factory.none(4), covered_bound)?;

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Toughnut - Domino Covering Problem ===\n");

    let n = 4; // 4x4 board
    let model = Toughnut::new();
    let mut options = Options::default();

    // Enable verbose to see what's happening
    println!("Test: Can we cover a {}x{} board with dominoes (opposite corners removed)?", n, n);
    println!("Formula: covering predicate\n");

    let bounds = model.bounds(n)?;

    // Debug: check bounds
    println!("Debug: Checking bounds...");
    if let Some(covered_upper) = bounds.upper_bound(&model.covered) {
        println!("  covered upper bound: {} tuples (arity {})", covered_upper.size(), covered_upper.arity());
        // Show first few tuples
        for (i, tuple) in covered_upper.iter().take(5).enumerate() {
            print!("    tuple {}: ", i);
            for j in 0..tuple.arity() {
                if let Some(atom) = tuple.atom(j) {
                    print!("{} ", atom);
                }
            }
            println!();
        }
    }
    if let Some(covered_lower) = bounds.lower_bound(&model.covered) {
        println!("  covered lower bound: {} tuples", covered_lower.size());
    }
    if let Some(cell_upper) = bounds.upper_bound(&model.cell) {
        println!("  cell bound: {} tuples (arity {})", cell_upper.size(), cell_upper.arity());
    }
    if let Some(ord_bound) = bounds.upper_bound(&model.ord) {
        println!("  ord bound: {} tuples (arity {})", ord_bound.size(), ord_bound.arity());
        for tuple in ord_bound.iter() {
            print!("    ");
            for j in 0..tuple.arity() {
                if let Some(atom) = tuple.atom(j) {
                    print!("{} ", atom);
                }
            }
            println!();
        }
    }

    println!("\nBuilding formula...");
    let formula = model.check_below_too_double_prime();

    println!("Solving...");
    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds)?;

    println!("\nResult: {}", if solution.is_sat() { "SAT (covering exists)" } else { "UNSAT (no covering)" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}
