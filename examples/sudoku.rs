//! Sudoku solver using kodkod-rs
//!
//! Encodes Sudoku puzzle as a relational logic problem and solves it.
//! This version solves 4x4 Sudoku (2x2 regions) for simplicity.

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Instance, Universe};
use kodkod_rs::solver::{Options, Solver};

fn main() {
    println!("=== 4x4 Sudoku Solver ===\n");

    // Create a 4x4 Sudoku solver
    let sudoku = Sudoku::new(2); // 2x2 regions = 4x4 grid

    // Define a simple puzzle (0 means empty cell)
    // Puzzle:
    //   1 2 | 3 4
    //   _ _ | _ _
    //  -----+-----
    //   _ _ | _ _
    //   4 3 | 2 1
    let puzzle = vec![
        (1, 1, 1), // row 1, col 1 = 1
        (1, 2, 2), // row 1, col 2 = 2
        (1, 3, 3), // row 1, col 3 = 3
        (1, 4, 4), // row 1, col 4 = 4
        (4, 1, 4), // row 4, col 1 = 4
        (4, 2, 3), // row 4, col 2 = 3
        (4, 3, 2), // row 4, col 3 = 2
        (4, 4, 1), // row 4, col 4 = 1
    ];

    println!("Puzzle:");
    print_puzzle(&puzzle, 4);

    // Create bounds
    let bounds = sudoku.bounds(&puzzle);

    // Create formula (rules of Sudoku)
    let formula = sudoku.rules();

    // Solve
    println!("\nSolving...");

    let solver = Solver::new(Options::default());

    match solver.solve(&formula, &bounds) {
        Ok(solution) => {
            if solution.is_sat() {
                println!("✓ Solution found!");
                println!(
                    "  Variables: {}, Clauses: {}",
                    solution.statistics().num_variables(),
                    solution.statistics().num_clauses()
                );
                println!(
                    "  Time: {}ms (translation: {}ms, solving: {}ms)",
                    solution.statistics().total_time(),
                    solution.statistics().translation_time(),
                    solution.statistics().solving_time()
                );

                // Extract and print the solution grid
                if let Some(instance) = solution.instance() {
                    println!("\nSolution:");
                    print_solution(instance, &sudoku);
                }
            } else {
                println!("✗ No solution exists (UNSAT)");
                println!(
                    "  Variables: {}, Clauses: {}",
                    solution.statistics().num_variables(),
                    solution.statistics().num_clauses()
                );
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

fn print_puzzle(clues: &[(usize, usize, usize)], n: usize) {
    let mut grid = vec![vec![0; n]; n];
    for &(row, col, val) in clues {
        grid[row - 1][col - 1] = val;
    }

    print_grid(&grid, n);
}

fn print_grid(grid: &[Vec<usize>], n: usize) {
    let r = (n as f64).sqrt() as usize;
    for (i, row) in grid.iter().enumerate() {
        if i > 0 && i % r == 0 {
            //print!("  ");
            for j in 0..n {
                if j > 0 && j % r == 0 {
                    print!("+");
                }
                print!("--");
            }
            println!();
        }
        for (j, &val) in row.iter().enumerate() {
            if j > 0 && j % r == 0 {
                print!("| ");
            }
            if val == 0 {
                print!("_ ");
            } else {
                print!("{} ", val);
            }
        }
        println!();
    }
}

fn print_solution(instance: &Instance, sudoku: &Sudoku) {
    let n = sudoku.n;
    let mut grid = vec![vec![0; n]; n];

    // Extract grid relation from instance
    if let Some(grid_tuples) = instance.get(&sudoku.grid) {
        // The grid relation is ternary: grid[row][col] = value
        // Encoded as tuples (row, col, value) where each is a "number" atom
        for tuple in grid_tuples.iter() {
            let atoms: Vec<_> = tuple.atoms().collect();
            if atoms.len() == 3 {
                // Parse the atom names (they are "1", "2", "3", "4" for 4x4)
                if let (Ok(row), Ok(col), Ok(val)) = (
                    atoms[0].parse::<usize>(),
                    atoms[1].parse::<usize>(),
                    atoms[2].parse::<usize>(),
                ) {
                    if row > 0 && row <= n && col > 0 && col <= n {
                        grid[row - 1][col - 1] = val;
                    }
                }
            }
        }
    }

    print_grid(&grid, n);
}

/// Sudoku puzzle encoder
struct Sudoku {
    number: Relation,
    grid: Relation,
    regions: Vec<Relation>,
    n: usize, // grid size (n×n)
    r: usize, // region size (r×r, where n = r²)
}

impl Sudoku {
    /// Creates a new Sudoku puzzle encoder
    ///
    /// For r=2: 4×4 grid with 2×2 regions
    /// For r=3: 9×9 grid with 3×3 regions
    fn new(r: usize) -> Self {
        assert!(r >= 2, "r must be at least 2");
        let n = r * r;

        let number = Relation::unary("number");
        let grid = Relation::ternary("grid");

        // Java: region = new Relation[r]
        // Creates r regions, not r×r!
        let mut regions = Vec::new();
        for i in 0..r {
            regions.push(Relation::unary(&format!("r{}", i + 1)));
        }

        Self {
            number,
            grid,
            regions,
            n,
            r,
        }
    }

    /// Returns grid[x][y] (the value at row x, column y)
    fn grid_at(&self, x: &Expression, y: &Expression) -> Expression {
        // grid[x][y] = y.join(x.join(grid))
        let x_join_grid = x.clone().join(Expression::from(self.grid.clone()));
        y.clone().join(x_join_grid)
    }

    /// Creates the Sudoku rules formula
    fn rules(&self) -> Formula {
        let x = Variable::unary("x");
        let y = Variable::unary("y");
        let decls = Decls::from(Decl::one_of(&x, &Expression::from(self.number.clone())))
            .and(Decl::one_of(&y, &Expression::from(self.number.clone())));

        let mut rules = Vec::new();

        // Rule 1: Each cell has exactly one value
        // forall x, y: number | some grid[x][y]
        rules.push(Formula::forall(
            decls.clone(),
            self.grid_at(&Expression::from(x.clone()), &Expression::from(y.clone()))
                .some(),
        ));

        // Rule 2: Each row has distinct values
        // forall x, y: number | no grid[x][y] & grid[x][number - y]
        let y_expr = Expression::from(y.clone());
        let other_cols = Expression::from(self.number.clone()).difference(y_expr.clone());

        rules.push(Formula::forall(
            decls.clone(),
            self.grid_at(&Expression::from(x.clone()), &y_expr)
                .intersection(self.grid_at(&Expression::from(x.clone()), &other_cols))
                .no(),
        ));

        // Rule 3: Each column has distinct values
        // forall x, y: number | no grid[x][y] & grid[number - x][y]
        let x_expr = Expression::from(x.clone());
        let other_rows = Expression::from(self.number.clone()).difference(x_expr.clone());

        rules.push(Formula::forall(
            decls,
            self.grid_at(&x_expr, &Expression::from(y.clone()))
                .intersection(self.grid_at(&other_rows, &Expression::from(y.clone())))
                .no(),
        ));

        // Rule 4: Each region has distinct values
        // Java: for(Relation rx : region) for(Relation ry: region)
        // Need DOUBLE loop over regions!
        for rx_region in &self.regions {
            for ry_region in &self.regions {
                let rx = Variable::unary("rx");
                let ry = Variable::unary("ry");
                let region_decls = Decls::from(Decl::one_of(&rx, &Expression::from(rx_region.clone())))
                    .and(Decl::one_of(&ry, &Expression::from(ry_region.clone())));

                let rx_expr = Expression::from(rx.clone());
                let ry_expr = Expression::from(ry.clone());

                let other_in_region_x =
                    Expression::from(rx_region.clone()).difference(rx_expr.clone());
                let other_in_region_y =
                    Expression::from(ry_region.clone()).difference(ry_expr.clone());

                rules.push(Formula::forall(
                    region_decls,
                    self.grid_at(&rx_expr, &ry_expr)
                        .intersection(self.grid_at(&other_in_region_x, &other_in_region_y))
                        .no(),
                ));
            }
        }

        Formula::and_all(rules)
    }

    /// Creates bounds for the puzzle
    fn bounds(&self, clues: &[(usize, usize, usize)]) -> Bounds {
        // Create universe: {1, 2, 3, ..., n}
        let atoms: Vec<String> = (1..=self.n).map(|i| i.to_string()).collect();
        let universe = Universe::new(&atoms.iter().map(|s| s.as_str()).collect::<Vec<_>>())
            .expect("Failed to create universe");

        let mut bounds = Bounds::new(universe.clone());
        let factory = bounds.universe().factory();

        // Bind number relation to all values {1..n}
        let number_tuples: Vec<Vec<&str>> = (1..=self.n)
            .map(|i| vec![atoms[i - 1].as_str()])
            .collect();
        let number_refs: Vec<&[&str]> = number_tuples.iter().map(|v| v.as_slice()).collect();

        let all_numbers = factory
            .tuple_set(&number_refs)
            .expect("Failed to create number tuples");

        bounds
            .bound_exactly(&self.number, all_numbers.clone())
            .expect("Failed to bind number");

        // Bind region relations
        // Each region is a partition of the numbers
        // For 4x4 (r=2): region[0] = {1,2}, region[1] = {3,4}
        // Java: bounds.boundExactly(region[i], f.range(f.tuple(i*r+1), f.tuple((i+1)*r)));
        for (i, region) in self.regions.iter().enumerate() {
            let start = i * self.r + 1;
            let end = (i + 1) * self.r;

            let region_atoms: Vec<&str> = (start..=end)
                .map(|idx| atoms[idx - 1].as_str())
                .collect();
            let region_tuples: Vec<Vec<&str>> = region_atoms.iter().map(|&a| vec![a]).collect();
            let region_refs: Vec<&[&str]> = region_tuples.iter().map(|v| v.as_slice()).collect();

            let region_set = factory
                .tuple_set(&region_refs)
                .expect("Failed to create region tuples");

            bounds
                .bound_exactly(region, region_set)
                .expect("Failed to bind region");
        }

        // Bind grid relation
        // Lower bound: given clues
        // Upper bound: all possible (row, col, val) triples
        let lower = if clues.is_empty() {
            factory.none(3)
        } else {
            let lower_tuples: Vec<Vec<&str>> = clues
                .iter()
                .map(|&(row, col, val)| {
                    vec![
                        atoms[row - 1].as_str(),
                        atoms[col - 1].as_str(),
                        atoms[val - 1].as_str(),
                    ]
                })
                .collect();
            let lower_refs: Vec<&[&str]> = lower_tuples.iter().map(|v| v.as_slice()).collect();

            factory
                .tuple_set(&lower_refs)
                .expect("Failed to create lower bound")
        };

        let upper = factory.all(3);

        bounds
            .bound(&self.grid, lower, upper)
            .expect("Failed to bind grid");

        bounds
    }
}
