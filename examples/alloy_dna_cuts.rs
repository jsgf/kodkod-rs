//! DNA cuts model
//!
//! Kodkod encoding of the DNA cuts model with cut links and join links.
//! Models base pairs (A-T, G-C), link sequences, and constraints on
//! cut chain lengths and cut link uniqueness.
//!
//! Following Java: kodkod.examples.alloy.DNACuts

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};
use rand::Rng;

struct DNACuts {
    base: Relation,
    link: Relation,
    cut_link: Relation,
    join_link: Relation,
    base_rel: Relation,
    next: Relation,
    partner: Relation,
    neighbor: Vec<Expression>,
}

impl DNACuts {
    fn new(cut_link_length: usize) -> Self {
        assert!(cut_link_length > 0);

        let mut neighbor = Vec::new();
        let next = Relation::binary("next");

        if cut_link_length > 1 {
            neighbor.push(Expression::from(next.clone()));
            for i in 1..cut_link_length - 1 {
                let prev = neighbor[i - 1].clone();
                neighbor.push(Expression::from(next.clone()).join(prev));
            }
        }

        Self {
            base: Relation::unary("Base"),
            link: Relation::unary("Link"),
            cut_link: Relation::unary("CutLink"),
            join_link: Relation::unary("JoinLink"),
            base_rel: Relation::binary("base"),
            next,
            partner: Relation::binary("partner"),
            neighbor,
        }
    }

    /// Returns declarations constraints
    fn declarations(&self) -> Formula {
        let l = Variable::unary("l");
        let f0 = Formula::forall(
            Decls::from(Decl::one_of(l.clone(), Expression::from(self.link.clone()))),
            Expression::from(l)
                .join(Expression::from(self.base_rel.clone()))
                .one()
        );

        let f1 = Expression::from(self.cut_link.clone())
            .union(Expression::from(self.join_link.clone()))
            .equals(Expression::from(self.link.clone()));

        let f2 = Expression::from(self.cut_link.clone())
            .intersection(Expression::from(self.join_link.clone()))
            .no();

        f0.and(f1).and(f2)
    }

    /// Returns the cutChainLength constraint
    fn cut_chain_length(&self) -> Formula {
        let c = Variable::unary("c");
        let mut ret = Formula::constant(false);

        for neighbor_expr in &self.neighbor {
            let constraint = Expression::from(c.clone())
                .join(neighbor_expr.clone())
                .in_set(Expression::from(self.join_link.clone()));
            ret = ret.or(constraint);
        }

        Formula::forall(
            Decls::from(Decl::one_of(c, Expression::from(self.cut_link.clone()))),
            ret
        )
    }

    /// Returns the cutLinkUniqueness constraint
    fn cut_link_uniqueness(&self) -> Formula {
        let c1 = Variable::unary("c1");
        let c2 = Variable::unary("c2");

        let f0 = Expression::from(c1.clone())
            .equals(Expression::from(c2.clone()))
            .not()
            .and(Expression::from(self.next.clone())
                .join(Expression::from(c1.clone()))
                .in_set(Expression::from(self.join_link.clone())))
            .and(Expression::from(self.next.clone())
                .join(Expression::from(c2.clone()))
                .in_set(Expression::from(self.join_link.clone())));

        let mut f = Expression::from(c1.clone())
            .join(Expression::from(self.base_rel.clone()))
            .in_set(Expression::from(c2.clone())
                .join(Expression::from(self.base_rel.clone()))
                .union(Expression::from(c2.clone())
                    .join(Expression::from(self.base_rel.clone()))
                    .join(Expression::from(self.partner.clone()))))
            .not();

        for neighbor_expr in &self.neighbor {
            let c1n = Expression::from(c1.clone()).join(neighbor_expr.clone());
            let c2n = Expression::from(c2.clone()).join(neighbor_expr.clone());

            f = f.or(c1n.clone().in_set(Expression::from(self.join_link.clone())));
            f = f.or(c2n.clone().in_set(Expression::from(self.join_link.clone())));
            f = f.or(c1n.join(Expression::from(self.base_rel.clone()))
                .in_set(c2n.clone().join(Expression::from(self.base_rel.clone()))
                    .union(c2n.join(Expression::from(self.base_rel.clone()))
                        .join(Expression::from(self.partner.clone()))))
                .not());
        }

        Formula::forall(
            Decls::from(Decl::one_of(c1.clone(), Expression::from(self.cut_link.clone())))
                .and(Decl::one_of(c2, Expression::from(self.cut_link.clone()))),
            f0.implies(f)
        )
    }

    /// Returns the show predicate
    fn show(&self) -> Formula {
        let f0 = Expression::from(self.base.clone())
            .in_set(Expression::from(self.link.clone())
                .join(Expression::from(self.base_rel.clone())));
        let f1 = Expression::from(self.join_link.clone()).some();
        let f2 = Expression::from(self.cut_link.clone()).some();

        self.declarations()
            .and(self.cut_chain_length())
            .and(self.cut_link_uniqueness())
            .and(f0)
            .and(f1)
            .and(f2)
    }

    /// Returns the bounds for n links
    fn bounds(&self, n: usize) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        let mut atoms = vec!["A", "T", "G", "C"];
        let link_names: Vec<String> = (0..n).map(|i| format!("Link{}", i)).collect();
        for name in &link_names {
            atoms.push(name.as_str());
        }

        let universe = Universe::new(&atoms)?;
        let factory = universe.factory();
        let mut bounds = Bounds::new(universe);

        let bases = factory.range(factory.tuple(&["A"])?, factory.tuple(&["C"])?)?;
        let links = if n > 0 {
            factory.range(
                factory.tuple(&["Link0"])?,
                factory.tuple(&[&format!("Link{}", n - 1)])?
            )?
        } else {
            factory.none(1)
        };

        bounds.bound_exactly(&self.base, bases)?;
        bounds.bound_exactly(&self.link, links.clone())?;
        bounds.bound(&self.cut_link, factory.none(1), links.clone())?;
        bounds.bound(&self.join_link, factory.none(1), links)?;

        // Random sequence for base assignments
        let mut rng = rand::thread_rng();
        let mut random_sequence = factory.none(2);
        for i in 0..n {
            let base_idx = rng.gen_range(0..4);
            let base_atom = ["A", "T", "G", "C"][base_idx];
            random_sequence.add(factory.tuple(&[&format!("Link{}", i), base_atom])?)?;
        }
        bounds.bound_exactly(&self.base_rel, random_sequence)?;

        // Partner relation
        let mut partners = factory.none(2);
        partners.add(factory.tuple(&["A", "T"])?)?;
        partners.add(factory.tuple(&["T", "A"])?)?;
        partners.add(factory.tuple(&["G", "C"])?)?;
        partners.add(factory.tuple(&["C", "G"])?)?;
        bounds.bound_exactly(&self.partner, partners)?;

        // Link ordering
        let mut link_ord = factory.none(2);
        for i in 1..n {
            link_ord.add(factory.tuple(&[
                &format!("Link{}", i - 1),
                &format!("Link{}", i)
            ])?)?;
        }
        bounds.bound_exactly(&self.next, link_ord)?;

        Ok(bounds)
    }
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 3 {
        eprintln!("Usage: {} <cut_chain_length> <num_links>", args[0]);
        std::process::exit(1);
    }

    let cut_length: usize = args[1].parse()
        .expect("cut_chain_length must be a positive integer");
    let num_links: usize = args[2].parse()
        .expect("num_links must be a non-negative integer");

    println!("=== DNA Cuts (cut_length={}, links={}) ===\n", cut_length, num_links);

    let model = DNACuts::new(cut_length);
    let formula = model.show();
    let bounds = model.bounds(num_links)?;

    println!("Solving...");
    let solver = Solver::new(Options::default());
    let solution = solver.solve(&formula, &bounds)?;

    println!("\nResult: {}", if solution.is_sat() { "SAT" } else { "UNSAT" });
    let stats = solution.statistics();
    println!("  Variables: {}, Clauses: {}", stats.num_variables(), stats.num_clauses());
    println!("  Translation: {}ms, Solving: {}ms, Total: {}ms",
        stats.translation_time(), stats.solving_time(), stats.total_time());

    Ok(())
}
