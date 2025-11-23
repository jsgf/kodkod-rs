//! Pigeonhole principle: n+1 pigeons cannot fit in n holes

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{atom_as_str, Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct Pigeonhole {
    pigeon: Relation,
    hole: Relation,
    hole_relation: Relation,
}

impl Pigeonhole {
    fn new() -> Self {
        Self {
            pigeon: Relation::unary("Pigeon"),
            hole: Relation::unary("Hole"),
            hole_relation: Relation::binary("hole"),
        }
    }

    /// hole is a function from Pigeon to Hole
    fn declarations(&self) -> Formula {
        // Every pigeon has exactly one hole: all p: Pigeon | one p.hole
        let p = Variable::unary("p");
        let p_expr = Expression::from(p.clone());
        let hole_expr = p_expr.join(Expression::from(self.hole_relation.clone()));

        let body = hole_expr.one();
        let decls = Decls::from(Decl::one_of(p.clone(), Expression::from(self.pigeon.clone())));

        Formula::forall(decls, body)
    }

    fn pigeon_per_hole(&self) -> Formula {
        // forall p1, p2: Pigeon |
        //   p1 != p2 => (p1.hole & p2.hole).no()
        // (different pigeons have different holes)
        let p1 = Variable::unary("p1");
        let p2 = Variable::unary("p2");

        let p1_expr = Expression::from(p1.clone());
        let p2_expr = Expression::from(p2.clone());

        let p1_hole = p1_expr.clone().join(Expression::from(self.hole_relation.clone()));
        let p2_hole = p2_expr.clone().join(Expression::from(self.hole_relation.clone()));

        // Body: (p1 != p2) => (no shared holes)
        let not_equal = p1_expr.equals(p2_expr).not();
        let no_shared = p1_hole.intersection(p2_hole).no();
        let body = not_equal.implies(no_shared);

        // Declarations: p1 in Pigeon, p2 in Pigeon
        let decls = Decls::from(Decl::one_of(p1, Expression::from(self.pigeon.clone())))
            .and(Decl::one_of(p2, Expression::from(self.pigeon.clone())));

        Formula::forall(decls, body)
    }

    fn bounds(&self, num_pigeons: usize, num_holes: usize) -> Result<Bounds, Box<dyn std::error::Error>> {
        // Build atom names
        let pigeon_atoms: Vec<String> = (0..num_pigeons)
            .map(|i| format!("Pigeon{}", i))
            .collect();
        let hole_atoms: Vec<String> = (0..num_holes)
            .map(|i| format!("Hole{}", i))
            .collect();

        // Create universe with all atoms
        let all_atoms: Vec<String> = pigeon_atoms.iter().chain(hole_atoms.iter()).cloned().collect();
        let atom_strs: Vec<&str> = all_atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();

        let mut bounds = Bounds::new(universe);

        // Pigeon bounds: exactly the pigeon atoms
        let pigeon_strs: Vec<&str> = pigeon_atoms.iter().map(|s| s.as_str()).collect();
        let pigeon_tuples: Vec<Vec<&str>> = pigeon_strs.iter().map(|&s| vec![s]).collect();
        let pigeon_refs: Vec<&[&str]> = pigeon_tuples.iter().map(|v| v.as_slice()).collect();
        bounds.bound_exactly(&self.pigeon, factory.tuple_set(&pigeon_refs)?)?;

        // Hole bounds: exactly the hole atoms
        let hole_strs: Vec<&str> = hole_atoms.iter().map(|s| s.as_str()).collect();
        let hole_tuples: Vec<Vec<&str>> = hole_strs.iter().map(|&s| vec![s]).collect();
        let hole_refs: Vec<&[&str]> = hole_tuples.iter().map(|v| v.as_slice()).collect();
        bounds.bound_exactly(&self.hole, factory.tuple_set(&hole_refs)?)?;

        // hole relation bounds: Pigeon x Hole (all possible pigeon-hole pairings)
        let pigeon_set = factory.tuple_set(&pigeon_refs)?;
        let hole_set = factory.tuple_set(&hole_refs)?;

        // Create cartesian product: Pigeon x Hole
        // This is done by creating all 2-tuples of the form (pigeon_atom, hole_atom)
        let mut product_tuples = Vec::new();
        for pigeon_tuple in pigeon_set.iter() {
            let pigeon_atoms: Vec<&str> = pigeon_tuple.atoms().filter_map(atom_as_str).collect();
            for hole_tuple in hole_set.iter() {
                let hole_atoms: Vec<&str> = hole_tuple.atoms().filter_map(atom_as_str).collect();
                let mut combined = pigeon_atoms.clone();
                combined.extend(hole_atoms);
                product_tuples.push(combined);
            }
        }
        let product_refs: Vec<&[&str]> = product_tuples.iter().map(|v| v.as_slice()).collect();
        let all_pairings = factory.tuple_set(&product_refs)?;

        bounds.bound(&self.hole_relation, factory.none(2), all_pairings)?;

        Ok(bounds)
    }
}

fn main() {
    println!("=== Pigeonhole Principle Solver ===\n");

    let test_cases = vec![
        (3, 3, "3 pigeons, 3 holes (should be SAT)"),
        (4, 3, "4 pigeons, 3 holes (should be UNSAT)"),
        (5, 4, "5 pigeons, 4 holes (should be UNSAT)"),
    ];

    for (num_pigeons, num_holes, description) in test_cases {
        println!("Test: {}", description);

        let model = Pigeonhole::new();
        let formula = model.declarations().and(model.pigeon_per_hole());

        match model.bounds(num_pigeons, num_holes) {
            Ok(bounds) => {
                let solver = Solver::new(Options::default());
                match solver.solve(&formula, &bounds) {
                    Ok(solution) => {
                        let status = if solution.is_sat() { "SAT" } else { "UNSAT" };
                        println!(
                            "  Result: {} (variables: {}, clauses: {})",
                            status,
                            solution.statistics().num_variables(),
                            solution.statistics().num_clauses()
                        );
                    }
                    Err(e) => println!("  Error solving: {}", e),
                }
            }
            Err(e) => println!("  Error creating bounds: {}", e),
        }
        println!();
    }
}
