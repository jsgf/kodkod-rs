//! Ceilings and Floors
//!
//! Paul Simon's "One Man's Ceiling Is Another Man's Floor" - Does the reverse hold?
//! Based on kodkod.examples.alloy.CeilingsAndFloors

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

pub struct CeilingsAndFloors {
    platform: Relation,
    man: Relation,
    ceiling: Relation,
    floor: Relation,
}

impl CeilingsAndFloors {
    pub fn new() -> Self {
        Self {
            platform: Relation::unary("Platform"),
            man: Relation::unary("Man"),
            ceiling: Relation::binary("ceiling"),
            floor: Relation::binary("floor"),
        }
    }

    /// Returns a formula that constrains the ceiling and floor
    /// relations to be functions from Man to Platform.
    /// FUNCTION(ceiling, Man, Platform) && FUNCTION(floor, Man, Platform)
    fn declarations(&self) -> Formula {
        // ceiling and floor are functions from Man to Platform
        // Encoded as: ceiling in Man->Platform && (all m: Man | one m.ceiling)

        let ceiling_domain_range = Expression::from(self.ceiling.clone())
            .in_set(Expression::from(self.man.clone()).product(Expression::from(self.platform.clone())));

        let m = Variable::unary("m_ceiling");
        let ceiling_functional = Formula::forall(
            Decls::from(Decl::one_of(m.clone(), Expression::from(self.man.clone()))),
            Expression::from(m).join(Expression::from(self.ceiling.clone())).one()
        );

        let floor_domain_range = Expression::from(self.floor.clone())
            .in_set(Expression::from(self.man.clone()).product(Expression::from(self.platform.clone())));

        let n = Variable::unary("n_floor");
        let floor_functional = Formula::forall(
            Decls::from(Decl::one_of(n.clone(), Expression::from(self.man.clone()))),
            Expression::from(n).join(Expression::from(self.floor.clone())).one()
        );

        Formula::and_all(vec![ceiling_domain_range, ceiling_functional, floor_domain_range, floor_functional])
    }

    /// Returns the belowToo constraint
    /// all m: Man | some n: Man | m.floor = n.ceiling
    fn below_too(&self) -> Formula {
        let m = Variable::unary("m0");
        let n = Variable::unary("n0");

        let m_floor_eq_n_ceiling = Expression::from(m.clone())
            .join(Expression::from(self.floor.clone()))
            .equals(Expression::from(n.clone()).join(Expression::from(self.ceiling.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(m, Expression::from(self.man.clone()))),
            Formula::exists(
                Decls::from(Decl::one_of(n, Expression::from(self.man.clone()))),
                m_floor_eq_n_ceiling
            )
        )
    }

    /// Returns the noSharing constraint.
    /// all m, n: Man | !(m = n) => !(m.floor = n.floor || m.ceiling = n.ceiling)
    fn no_sharing(&self) -> Formula {
        let m = Variable::unary("m1");
        let n = Variable::unary("n1");

        let floor_shared = Expression::from(m.clone())
            .join(Expression::from(self.floor.clone()))
            .equals(Expression::from(n.clone()).join(Expression::from(self.floor.clone())));

        let ceiling_shared = Expression::from(m.clone())
            .join(Expression::from(self.ceiling.clone()))
            .equals(Expression::from(n.clone()).join(Expression::from(self.ceiling.clone())));

        let body = floor_shared.or(ceiling_shared);

        Formula::forall(
            Decls::from(Decl::one_of(m.clone(), Expression::from(self.man.clone())))
                .and(Decl::one_of(n.clone(), Expression::from(self.man.clone()))),
            Expression::from(m).equals(Expression::from(n)).not().implies(body.not())
        )
    }

    /// Returns the paulSimon constraint.
    /// all m: Man | some n: Man | n.floor = m.ceiling
    fn paul_simon(&self) -> Formula {
        let m = Variable::unary("m2");
        let n = Variable::unary("n2");

        let n_floor_eq_m_ceiling = Expression::from(n.clone())
            .join(Expression::from(self.floor.clone()))
            .equals(Expression::from(m.clone()).join(Expression::from(self.ceiling.clone())));

        Formula::forall(
            Decls::from(Decl::one_of(m, Expression::from(self.man.clone()))),
            Formula::exists(
                Decls::from(Decl::one_of(n, Expression::from(self.man.clone()))),
                n_floor_eq_m_ceiling
            )
        )
    }

    /// Returns the belowToo'' constraint.
    /// declarations() &&  paulSimon() && noSharing() && !belowToo()
    pub fn check_below_too_double_prime(&self) -> Formula {
        Formula::and_all(vec![
            self.declarations(),
            self.paul_simon(),
            self.no_sharing(),
            self.below_too().not()
        ])
    }

    /// Returns the belowToo assertion.
    /// declarations() && paulSimon() && !belowToo()
    pub fn check_below_too_assertion(&self) -> Formula {
        Formula::and_all(vec![
            self.declarations(),
            self.paul_simon(),
            self.below_too().not()
        ])
    }

    /// Creates bounds for the problem using the given number of platforms and men.
    pub fn bounds(&self, platforms: usize, men: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms = Vec::new();
        for i in 0..men {
            atoms.push(format!("Man{}", i));
        }
        for i in 0..platforms {
            atoms.push(format!("Platform{}", i));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        let man_max = format!("Man{}", men - 1);
        let platform_max = format!("Platform{}", platforms - 1);

        let platform_bound = factory.range(
            factory.tuple(&["Platform0"])?,
            factory.tuple(&[platform_max.as_str()])?
        )?;

        let man_bound = factory.range(
            factory.tuple(&["Man0"])?,
            factory.tuple(&[man_max.as_str()])?
        )?;

        let ceiling_bound = factory.area(
            factory.tuple(&["Man0", "Platform0"])?,
            factory.tuple(&[man_max.as_str(), platform_max.as_str()])?
        )?;

        let floor_bound = factory.area(
            factory.tuple(&["Man0", "Platform0"])?,
            factory.tuple(&[man_max.as_str(), platform_max.as_str()])?
        )?;

        bounds.bound(&self.platform, factory.none(1), platform_bound)?;
        bounds.bound(&self.man, factory.none(1), man_bound)?;
        bounds.bound(&self.ceiling, factory.none(2), ceiling_bound)?;
        bounds.bound(&self.floor, factory.none(2), floor_bound)?;

        Ok(bounds)
    }
}

fn run() -> Result<(), kodkod_rs::error::KodkodError> {
    println!("=== Ceilings and Floors ===\n");
    println!("Paul Simon: 'One Man's Ceiling Is Another Man's Floor'\n");

    let model = CeilingsAndFloors::new();
    let options = Options::default();

    // Test 1: Check BelowToo assertion for 2 men, 2 platforms
    println!("Test 1: Check BelowToo assertion for 2 men, 2 platforms");
    println!("(expects counterexample)\n");

    let formula1 = model.check_below_too_assertion();
    let bounds1 = model.bounds(2, 2)?;

    let solver = Solver::new(options.clone());
    let solution1 = solver.solve(&formula1, &bounds1)?;

    println!("Result: {}", if solution1.is_sat() { "SAT (counterexample found)" } else { "UNSAT (assertion holds)" });
    let stats1 = solution1.statistics();
    println!("  Variables: {}, Clauses: {}", stats1.num_variables(), stats1.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms\n",
        stats1.translation_time(), stats1.solving_time(), stats1.total_time());

    // Test 2: Check BelowToo'' with NoSharing for 5 men, 5 platforms
    println!("Test 2: Check BelowToo'' with NoSharing for 5 men, 5 platforms");
    println!("(expects no counterexample)\n");

    let formula2 = model.check_below_too_double_prime();
    let bounds2 = model.bounds(5, 5)?;
    let solution2 = solver.solve(&formula2, &bounds2)?;

    println!("Result: {}", if solution2.is_sat() { "SAT (counterexample found)" } else { "UNSAT (assertion holds)" });
    let stats2 = solution2.statistics();
    println!("  Variables: {}, Clauses: {}", stats2.num_variables(), stats2.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats2.translation_time(), stats2.solving_time(), stats2.total_time());

    Ok(())
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    run()
}

#[test]
fn test_alloy_ceilings_and_floors_runs() {
    // Test that the example runs without panicking
    run().unwrap();
}
