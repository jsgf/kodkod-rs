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

//! A Kodkod encoding of the social golfer problem.
//!
//! The problem: Schedule groups of golfers playing over multiple weeks such that
//! no two golfers play in the same group more than once.

use kodkod_rs::ast::{Decl, Decls, Expression, Formula, Relation, Variable};
use kodkod_rs::instance::{atom_as_str, Bounds, Universe};
use kodkod_rs::solver::{Options, Solver};
use std::time::Instant;

/// Model of the social golfer problem
struct SocialGolfer {
    plays: Relation,
    player: Relation,
    week: Relation,
    group: Relation,
    size: Relation,
}

impl SocialGolfer {
    /// Constructs a new instance of the social golfer problem
    fn new() -> Self {
        Self {
            plays: Relation::ternary("plays"),
            player: Relation::unary("player"),
            week: Relation::unary("week"),
            group: Relation::unary("group"),
            size: Relation::unary("size"),
        }
    }

    /// Returns the constraints on the playing schedule
    fn schedule(&self) -> Formula {
        let p = Variable::unary("p");
        let w = Variable::unary("w");
        let g = Variable::unary("g");

        // Each player plays in exactly one group each week
        let f0_body = Expression::from(w.clone())
            .join(Expression::from(self.plays.clone()))
            .join(Expression::from(p.clone()))
            .one();
        let f0_decls = Decls::from(Decl::one_of(p.clone(), Expression::from(self.player.clone())))
            .and(Decl::one_of(w.clone(), Expression::from(self.week.clone())));
        let f0 = Formula::forall(f0_decls, f0_body);

        // Each group has the specified size each week
        let groupsize = Expression::from(self.size.clone()).sum_int();
        let f1_body = Expression::from(g.clone())
            .join(Expression::from(w.clone()).join(Expression::from(self.plays.clone())))
            .cardinality()
            .eq(groupsize);
        let f1_decls = Decls::from(Decl::one_of(g, Expression::from(self.group.clone())))
            .and(Decl::one_of(w, Expression::from(self.week.clone())));
        let f1 = Formula::forall(f1_decls, f1_body);

        // No two players play together more than once
        let p1 = Variable::unary("p1");
        let p2 = Variable::unary("p2");
        let f2_body = Expression::from(self.plays.clone())
            .join(Expression::from(p1.clone()))
            .intersection(Expression::from(self.plays.clone()).join(Expression::from(p2.clone())))
            .lone();
        let f2_decls = Decls::from(Decl::one_of(p1.clone(), Expression::from(self.player.clone())))
            .and(Decl::one_of(
                p2.clone(),
                Expression::from(self.player.clone()).difference(Expression::from(p1)),
            ));
        let f2 = Formula::forall(f2_decls, f2_body);

        Formula::and_all(vec![f0, f1, f2])
    }

    /// Returns the bounds for the scheduling problem
    fn bounds(
        &self,
        players: usize,
        groups: usize,
        weeks: usize,
        size: i32,
    ) -> Result<Bounds, kodkod_rs::error::KodkodError> {
        assert!(players >= 1 && groups >= 1 && weeks >= 1 && size >= 1);

        let mut atoms = Vec::new();

        // Players: p0, p1, ...
        for i in 0..players {
            atoms.push(format!("p{}", i));
        }

        // Groups: g0, g1, ...
        for i in 0..groups {
            atoms.push(format!("g{}", i));
        }

        // Weeks: w0, w1, ...
        for i in 0..weeks {
            atoms.push(format!("w{}", i));
        }

        // Size atom
        atoms.push(size.to_string());

        let atom_strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let universe = Universe::new(&atom_strs)?;
        let factory = universe.factory();

        let mut bounds = Bounds::new(universe);

        // Bind size relations
        let size_atom = size.to_string();
        bounds.bound_exactly(&self.size, factory.tuple_set(&[&[&size_atom]])?)?;

        // Bind player relation
        bounds.bound_exactly(
            &self.player,
            factory.range(
                factory.tuple(&[&format!("p0")])?,
                factory.tuple(&[&format!("p{}", players - 1)])?,
            )?,
        )?;

        // Bind group relation
        bounds.bound_exactly(
            &self.group,
            factory.range(
                factory.tuple(&[&format!("g0")])?,
                factory.tuple(&[&format!("g{}", groups - 1)])?,
            )?,
        )?;

        // Bind week relation
        bounds.bound_exactly(
            &self.week,
            factory.range(
                factory.tuple(&[&format!("w0")])?,
                factory.tuple(&[&format!("w{}", weeks - 1)])?,
            )?,
        )?;

        // Bind plays relation (week x group x player)
        let week_bound = bounds.upper_bound(&self.week).unwrap();
        let group_bound = bounds.upper_bound(&self.group).unwrap();
        let player_bound = bounds.upper_bound(&self.player).unwrap();

        let plays_bound = week_bound
            .product(&group_bound)?
            .product(&player_bound)?;

        bounds.bound(&self.plays, factory.none(3), plays_bound)?;

        Ok(bounds)
    }

    /// Print the solution
    fn print(&self, solution: &kodkod_rs::solver::Solution) {
        if let Some(instance) = solution.instance() {
            println!("SAT");
            println!("{:?}", solution.statistics());
            println!("Schedule:");

            if let Some(plays_tuples) = instance.tuples(&self.plays) {
                for tuple in plays_tuples.iter() {
                    if let (Some(week), Some(group), Some(player)) =
                        (tuple.atom(0), tuple.atom(1), tuple.atom(2))
                    {
                        let w = atom_as_str(week).unwrap_or("");
                        let g = atom_as_str(group).unwrap_or("");
                        let p = atom_as_str(player).unwrap_or("");
                        print!("{}->{}->{}; ", w, g, p);
                    }
                }
                println!();
            }
        } else {
            println!("{:?}", solution);
        }
    }
}

fn usage() {
    eprintln!("Usage: csp_social_golfer <players> <groups> <weeks> <group_size>");
    std::process::exit(1);
}

fn main() -> Result<(), kodkod_rs::error::KodkodError> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 5 {
        usage();
    }

    let players: usize = args[1].parse().unwrap_or_else(|_| {
        usage();
        unreachable!()
    });

    let groups: usize = args[2].parse().unwrap_or_else(|_| {
        usage();
        unreachable!()
    });

    let weeks: usize = args[3].parse().unwrap_or_else(|_| {
        usage();
        unreachable!()
    });

    let size: i32 = args[4].parse().unwrap_or_else(|_| {
        usage();
        unreachable!()
    });

    if players < 1 || groups < 1 || weeks < 1 || size < 1 {
        usage();
    }

    let start = Instant::now();

    let model = SocialGolfer::new();
    let formula = model.schedule();
    let bounds = model.bounds(players, groups, weeks, size)?;

    let mut options = Options::default();
    options.symmetry_breaking = 1000;
    let total = groups * weeks;
    let bitwidth = if total > 0 {
        let lz = total.leading_zeros();
        32_usize.saturating_sub(lz as usize).max(1)
    } else {
        1
    };
    options.bool_options.bitwidth = bitwidth;

    let solver = Solver::new(options);
    let solution = solver.solve(&formula, &bounds)?;

    model.print(&solution);

    let elapsed = start.elapsed();
    println!("Total time: {} ms", elapsed.as_millis());

    Ok(())
}
