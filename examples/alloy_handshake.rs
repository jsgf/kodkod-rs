//! Handshake puzzle: identify people by hand-shaking patterns
//!
//! A logic puzzle where people shake hands with constraints on spouse relationships.
//! Different people shake different numbers of hands (except for one).

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};

struct Handshake {
    person: Relation,
    hilary: Relation,
    jocelyn: Relation,
    shaken: Relation,
    spouse: Relation,
}

impl Handshake {
    fn new() -> Self {
        Self {
            person: Relation::unary("Person"),
            hilary: Relation::unary("Hilary"),
            jocelyn: Relation::unary("Jocelyn"),
            shaken: Relation::binary("shaken"),
            spouse: Relation::binary("spouse"),
        }
    }

    /// Declarations: structure of the model
    fn declarations(&self) -> Formula {
        // spouse is a function: Person -> Person
        let p = Variable::unary("p");
        let spouse_fn = Expression::from(p.clone())
            .join(Expression::from(self.spouse.clone()))
            .one();
        let spouse_fn_formula = Formula::forall(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.person.clone()))),
            spouse_fn
        );

        // shaken is in Person x Person
        let shaken_in = Expression::from(self.shaken.clone())
            .in_set(
                Expression::from(self.person.clone())
                    .product(Expression::from(self.person.clone()))
            );

        // Hilary and Jocelyn are singletons
        let hilary_one = Expression::from(self.hilary.clone()).one();
        let jocelyn_one = Expression::from(self.jocelyn.clone()).one();

        spouse_fn_formula.and(shaken_in).and(hilary_one).and(jocelyn_one)
    }

    /// ShakingProtocol facts
    fn shaking_protocol(&self) -> Formula {
        let p = Variable::unary("p");
        let q = Variable::unary("q");

        let p_expr = Expression::from(p.clone());
        let q_expr = Expression::from(q.clone());

        // Nobody shakes own or spouse's hand
        // all p: Person | no (p + p.spouse) & p.shaken
        let p_and_spouse = p_expr.clone()
            .union(p_expr.clone().join(Expression::from(self.spouse.clone())));
        let p_shaken = p_expr.clone().join(Expression::from(self.shaken.clone()));
        let f1_body = p_and_spouse.intersection(p_shaken).no();
        let f1 = Formula::forall(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.person.clone()))),
            f1_body
        );

        // If p shakes q, q shakes p
        // all p, q: Person | p in q.shaken => q in p.shaken
        let p_in_q_shaken = p_expr.clone()
            .in_set(q_expr.clone().join(Expression::from(self.shaken.clone())));
        let q_in_p_shaken = q_expr.clone()
            .in_set(p_expr.join(Expression::from(self.shaken.clone())));
        let f2_body = p_in_q_shaken.implies(q_in_p_shaken);
        let f2 = Formula::forall(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.person.clone())))
                .and(Decl::one_of(q.clone(), Expression::from(self.person.clone()))),
            f2_body
        );

        f1.and(f2)
    }

    /// Spouses facts
    fn spouses(&self) -> Formula {
        let p = Variable::unary("p");
        let q = Variable::unary("q");

        let p_expr = Expression::from(p.clone());
        let q_expr = Expression::from(q.clone());
        let spouse_rel = Expression::from(self.spouse.clone());

        // Different people constraints
        // all disj p, q: Person { ... }
        let disjoint = p_expr.clone().intersection(q_expr.clone()).no();

        // if q is p's spouse, p is q's spouse
        let p_spouse_eq_q = p_expr.clone().join(spouse_rel.clone()).equals(q_expr.clone());
        let q_spouse_eq_p = q_expr.clone().join(spouse_rel.clone()).equals(p_expr.clone());
        let f1 = p_spouse_eq_q.implies(q_spouse_eq_p);

        // no spouse sharing
        let f2 = p_expr.clone().join(spouse_rel.clone())
            .equals(q_expr.clone().join(spouse_rel.clone()))
            .not();

        let disj_implies_body = disjoint.implies(f1.and(f2));
        let disj_implies = Formula::forall(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.person.clone())))
                .and(Decl::one_of(q.clone(), Expression::from(self.person.clone()))),
            disj_implies_body
        );

        // All people constraints
        let p = Variable::unary("p");
        let p_expr = Expression::from(p.clone());
        let spouse_rel = Expression::from(self.spouse.clone());

        // a person is his or her spouse's spouse
        let f3 = p_expr.clone()
            .join(spouse_rel.clone())
            .join(spouse_rel.clone())
            .equals(p_expr.clone());

        // nobody is his or her own spouse
        let f4 = p_expr.clone()
            .equals(p_expr.join(spouse_rel))
            .not();

        let all_p = Formula::forall(
            Decls::from(Decl::one_of(p.clone(), Expression::from(self.person.clone()))),
            f3.and(f4)
        );

        disj_implies.and(all_p)
    }

    /// Puzzle predicate
    fn puzzle(&self) -> Formula {
        let p = Variable::unary("p");
        let q = Variable::unary("q");

        let p_expr = Expression::from(p.clone());
        let q_expr = Expression::from(q.clone());

        // everyone but Jocelyn has shaken a different number of hands
        // all disj p,q: Person - Jocelyn | #p.shaken != #q.shaken
        let not_jocelyn = Expression::from(self.person.clone())
            .difference(Expression::from(self.jocelyn.clone()));

        let p_shaken_count = p_expr.clone().join(Expression::from(self.shaken.clone())).count();
        let q_shaken_count = q_expr.clone().join(Expression::from(self.shaken.clone())).count();

        let different_counts = p_shaken_count.eq(q_shaken_count).not();

        let disjoint = p_expr.clone().intersection(q_expr.clone()).no();
        let puzzle1_body = disjoint.implies(different_counts);
        let puzzle1 = Formula::forall(
            Decls::from(Decl::one_of(p, not_jocelyn.clone()))
                .and(Decl::one_of(q, not_jocelyn)),
            puzzle1_body
        );

        // Hilary's spouse is Jocelyn
        let puzzle2 = Expression::from(self.hilary.clone())
            .join(Expression::from(self.spouse.clone()))
            .equals(Expression::from(self.jocelyn.clone()));

        puzzle1.and(puzzle2)
    }

    fn bounds(&self, num_persons: usize) -> Result<Bounds, Box<dyn std::error::Error>> {
        let mut atoms = Vec::new();
        atoms.push("Hilary".to_string());
        atoms.push("Jocelyn".to_string());
        for i in 2..num_persons {
            atoms.push(format!("Person{}", i));
        }

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();

        let mut bounds = Bounds::new(universe);

        // Person bounds: all atoms
        let person_tuples: Vec<Vec<&str>> = atom_strs.iter().map(|&s| vec![s]).collect();
        let person_refs: Vec<&[&str]> = person_tuples.iter().map(|v| v.as_slice()).collect();
        bounds.bound_exactly(&self.person, factory.tuple_set(&person_refs)?)?;

        // Hilary and Jocelyn bounds: singletons
        bounds.bound_exactly(&self.hilary, factory.tuple_set(&[&["Hilary"][..]])?)?;
        bounds.bound_exactly(&self.jocelyn, factory.tuple_set(&[&["Jocelyn"][..]])?)?;

        // spouse and shaken bounds: all binary tuples
        let all_binary = factory.all(2);
        bounds.bound(&self.spouse, factory.none(2), all_binary.clone())?;
        bounds.bound(&self.shaken, factory.none(2), all_binary)?;

        Ok(bounds)
    }
}

fn main() {
    println!("=== Handshake Puzzle Solver ===\n");

    for num_persons in 2..=6 {
        println!("Test: {} persons", num_persons);

        let model = Handshake::new();
        let formula = model.declarations()
            .and(model.shaking_protocol())
            .and(model.spouses())
            .and(model.puzzle());

        match model.bounds(num_persons) {
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

                        if solution.is_sat() {
                            if let Some(inst) = solution.instance() {
                                if let Some(shaken_tuples) = inst.get(&model.shaken) {
                                    println!("  Solution found with {} handshakes", shaken_tuples.size());
                                }
                            }
                        }
                    }
                    Err(e) => println!("  Error solving: {}", e),
                }
            }
            Err(e) => println!("  Error creating bounds: {}", e),
        }
        println!();
    }
}
