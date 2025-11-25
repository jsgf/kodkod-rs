/*
 * Kodkod -- Copyright (c) 2005-2012, Emina Torlak
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

//! Synthesis demo.
//!
//! Following Java: kodkod.examples.bmc.ListSynth

use kodkod_rs::ast::{Expression, Formula, Relation, Variable, Decls, Decl};
use kodkod_rs::solver::{Solution, Solver, Options};
use kodkod_rs::instance::{Bounds, Universe};

// Import the ListEncoding module and ListCheck
#[path = "bmc_list_encoding/mod.rs"]
mod bmc_list_encoding;

#[path = "bmc_list_check/mod.rs"]
mod bmc_list_check;

use bmc_list_encoding::ListEncoding;
use bmc_list_check::ListCheck;

struct ListSynth {
    encoding: ListEncoding,
    // Syntax relations - represent the syntax elements themselves
    hole: Relation,
    head_stx: Relation,
    near_node0_stx: Relation,
    mid_node0_stx: Relation,
    far_node0_stx: Relation,
}

impl ListSynth {
    fn new() -> Self {
        // Introduce relations that we'll use for reflection; that is, a relation
        // that represents the syntax "this.head", "nearNode0", etc.
        // Also introduce a relation that maps each piece of syntax to its meaning.
        ListSynth {
            encoding: ListEncoding::new(),
            head_stx: Relation::unary("\"head\""),
            near_node0_stx: Relation::unary("\"nearNode0\""),
            mid_node0_stx: Relation::unary("\"midNode0\""),
            far_node0_stx: Relation::unary("\"farNode0\""),
            // Represents the hole for "farNode0" in "next0 = update(next, nearNode0 -> farNode0)"
            hole: Relation::unary("\"??\""),
        }
    }

    /// Maps syntax to semantics
    fn meaning(&self) -> Expression {
        let nil_expr: Expression = self.encoding.nil.clone().into();
        let head_stx_expr: Expression = self.head_stx.clone().into();
        let near_node0_stx_expr: Expression = self.near_node0_stx.clone().into();
        let mid_node0_stx_expr: Expression = self.mid_node0_stx.clone().into();
        let far_node0_stx_expr: Expression = self.far_node0_stx.clone().into();

        let this_list_expr: Expression = self.encoding.this_list.clone().into();
        let head_expr: Expression = self.encoding.head.clone().into();

        Expression::union_all(vec![
            nil_expr.clone().product(nil_expr),
            head_stx_expr.product(this_list_expr.join(head_expr)),
            near_node0_stx_expr.product(self.encoding.near_node0()),
            mid_node0_stx_expr.product(self.encoding.mid_node0()),
            far_node0_stx_expr.product(self.encoding.far_node0()),
        ])
    }

    /// Override next0 to use the hole
    fn next0(&self) -> Expression {
        let next_expr: Expression = self.encoding.next.clone().into();
        let hole_expr: Expression = self.hole.clone().into();

        // next0 := update(next, nearNode0 -> ??.meaning)
        next_expr.override_with(
            self.encoding.near_node0().product(hole_expr.join(self.meaning()))
        )
    }

    /// Compute guard0 using our next0
    fn guard0(&self) -> Formula {
        let nil_expr: Expression = self.encoding.nil.clone().into();
        self.far_node0().equals(nil_expr).not()
    }

    /// Compute next1 using our next0
    fn next1(&self) -> Expression {
        self.next0().override_with(self.encoding.mid_node0().product(self.encoding.near_node0()))
    }

    /// Compute far_node0 using base encoding
    fn far_node0(&self) -> Expression {
        self.encoding.far_node0()
    }

    /// Compute far_node1 using our next1
    fn far_node1(&self) -> Expression {
        self.far_node0().join(self.next1())
    }

    /// Compute next2 using our versions
    fn next2(&self) -> Expression {
        self.guard0().then_else(self.next1(), self.next0())
    }

    /// Compute near_node2 using our versions
    fn near_node2(&self) -> Expression {
        self.guard0().then_else(self.encoding.near_node1(), self.encoding.near_node0())
    }

    /// Compute mid_node2 using our versions
    fn mid_node2(&self) -> Expression {
        self.guard0().then_else(self.encoding.mid_node1(), self.encoding.mid_node0())
    }

    /// Compute far_node2 using our versions
    fn far_node2(&self) -> Expression {
        self.guard0().then_else(self.far_node1(), self.far_node0())
    }

    /// Loop guard using our far_node2
    fn loop_guard(&self) -> Formula {
        let nil_expr: Expression = self.encoding.nil.clone().into();
        self.far_node2().equals(nil_expr)
    }

    /// Compute next3 using our versions
    fn next3(&self) -> Expression {
        self.next2().override_with(self.mid_node2().product(self.near_node2()))
    }

    /// Compute head0 using our versions
    fn head0(&self) -> Expression {
        let this_list_expr: Expression = self.encoding.this_list.clone().into();
        let head_expr: Expression = self.encoding.head.clone().into();
        head_expr.override_with(this_list_expr.product(self.mid_node2()))
    }

    fn synth_spec(&self) -> Formula {
        // Make sure that our hole is a singleton
        let hole_constraint = Expression::from(self.hole.clone()).one();

        let pre = self.encoding.pre();
        let loop_guard = self.loop_guard();

        // FULL post() with next NOT exactly bounded
        let next3 = self.next3();
        let head0 = self.head0();
        let post = self.encoding.post_with(next3, head0);

        Formula::and_all(vec![
            pre,
            loop_guard,
            post,
            hole_constraint,
        ])
    }

    fn universe(&self, size: usize) -> Result<Universe, kodkod_rs::KodkodError> {
        let mut elts = Vec::new();
        elts.push("l0");

        let mut nodes = Vec::with_capacity(size);
        for i in 0..size {
            nodes.push(format!("n{i}"));
        }

        let mut strings = Vec::with_capacity(size);
        for i in 0..size {
            strings.push(format!("s{i}"));
        }

        elts.extend(nodes.iter().map(|s| s.as_str()));
        elts.extend(strings.iter().map(|s| s.as_str()));
        elts.push("nil");

        // NOTE: In Java, the syntax relations are added as Relation objects to the universe.
        // In Rust, we can't add Relation objects to the universe (they're not atoms).
        // Instead we use string representations. This may be the source of the bug.
        // Java: elts.add(headStx);  // adds the Relation object as an atom
        // Rust: elts.push("\"head\"");  // adds a string representation
        elts.push("\"head\"");
        elts.push("\"nearNode0\"");
        elts.push("\"midNode0\"");
        elts.push("\"farNode0\"");

        Universe::new(&elts)
    }

    fn synth_bounds(&self, size: usize) -> Bounds {
        // Get counterexample from checker
        let checker = ListCheck::new();
        let sol = checker.check(size);
        let cex = match sol {
            Solution::Sat { instance, ..} => instance,
            _ => panic!("Expected SAT solution from ListCheck"),
        };

        // Create bounds using OUR universe (with syntax atoms), not encoding's universe
        let u = self.universe(size).expect("Failed to create universe");
        eprintln!("\nDEBUG: Synth universe atoms:");
        for (i, (_, atom)) in u.iter_atoms().enumerate() {
            eprintln!("  {}: {}", i, kodkod_rs::instance::atom_as_str(atom).unwrap_or("<non-string>"));
        }

        let mut b = Bounds::new(u);
        let t = b.universe().factory();
        let max = size - 1;

        // Set up base bounds just like ListEncoding.bounds() does
        // In Java, b.bound(rel, set) means lower=empty, upper=set (NOT exact!)
        let list_set = t.tuple_set(&[&["l0"]]).unwrap();
        b.bound(&self.encoding.list, t.none(1), list_set).unwrap();

        let node_set = t.range(t.tuple(&["n0"]).unwrap(), t.tuple(&[&format!("n{max}")]).unwrap()).unwrap();
        b.bound(&self.encoding.node, t.none(1), node_set).unwrap();

        let string_set = t.range(t.tuple(&["s0"]).unwrap(), t.tuple(&[&format!("s{max}")]).unwrap()).unwrap();
        b.bound(&self.encoding.string, t.none(1), string_set).unwrap();

        b.bound_exactly(&self.encoding.nil, t.tuple_set(&[&["nil"]]).unwrap()).unwrap();

        // Set initial bounds for relations that will be bound exactly from counterexample
        // These must be bounded first before we can call bound_exactly()
        let mut ran = t.range(t.tuple(&["n0"]).unwrap(), t.tuple(&[&format!("n{max}")]).unwrap()).unwrap();
        ran.add(t.tuple(&["nil"]).unwrap()).unwrap();

        let list_upper = b.upper_bound(&self.encoding.list).unwrap().clone();
        let node_upper = b.upper_bound(&self.encoding.node).unwrap().clone();

        b.bound(&self.encoding.this_list, t.none(1), list_upper.clone()).unwrap();
        b.bound(&self.encoding.head, t.none(2), list_upper.product(&ran).unwrap()).unwrap();
        b.bound(&self.encoding.next, t.none(2), node_upper.clone().product(&ran).unwrap()).unwrap();

        let mut ran_str = t.range(t.tuple(&["s0"]).unwrap(), t.tuple(&[&format!("s{max}")]).unwrap()).unwrap();
        ran_str.add(t.tuple(&["nil"]).unwrap()).unwrap();
        b.bound(&self.encoding.data, t.none(2), node_upper.product(&ran_str).unwrap()).unwrap();

        // Now add bounds for synthesis-specific relations
        // Bound the hole to the set of syntax options
        let mut hole_bound = t.none(1);
        hole_bound.add(t.tuple(&["nil"]).unwrap()).unwrap();
        hole_bound.add(t.tuple(&["\"head\""]).unwrap()).unwrap();
        hole_bound.add(t.tuple(&["\"nearNode0\""]).unwrap()).unwrap();
        hole_bound.add(t.tuple(&["\"midNode0\""]).unwrap()).unwrap();
        hole_bound.add(t.tuple(&["\"farNode0\""]).unwrap()).unwrap();
        b.bound(&self.hole, t.none(1), hole_bound).expect("Failed to bound hole");

        // Bind syntax relations to themselves
        b.bound_exactly(&self.head_stx, t.tuple_set(&[&["\"head\""]]).unwrap()).unwrap();
        b.bound_exactly(&self.near_node0_stx, t.tuple_set(&[&["\"nearNode0\""]]).unwrap()).unwrap();
        b.bound_exactly(&self.mid_node0_stx, t.tuple_set(&[&["\"midNode0\""]]).unwrap()).unwrap();
        b.bound_exactly(&self.far_node0_stx, t.tuple_set(&[&["\"farNode0\""]]).unwrap()).unwrap();

        // Copy counterexample values (these will be translated to our universe)
        eprintln!("DEBUG: Copying bounds from counterexample...");
        eprintln!("  cex universe size: {}", cex.universe().size());
        eprintln!("  synth universe size: {}", b.universe().size());

        // Print the counterexample next relation
        if let Some(next_in_cex) = cex.tuples(&checker.encoding.next) {
            eprintln!("\nDEBUG: Counterexample 'next' relation:");
            for tuple in next_in_cex.iter() {
                if let (Some(from), Some(to)) = (tuple.atom(0), tuple.atom(1)) {
                    use kodkod_rs::instance::atom_as_str;
                    eprintln!("  {} -> {}",
                        atom_as_str(from).unwrap_or("?"),
                        atom_as_str(to).unwrap_or("?"));
                }
            }
        }

        let next_tuples = self.encoding.copy_from(&t, cex.tuples(&checker.encoding.next).expect("next tuples"));
        eprintln!("  next: {} tuples", next_tuples.size());
        // WORKAROUND: Don't bind next exactly - causes translator bug with acyclic(next3)
        // When next is exactly bounded, acyclic(next3) where next3 uses next.override_with()
        // incorrectly reduces to constant FALSE during translation
        // TODO: Fix translator's handling of acyclic() on complex override expressions
        // b.bound_exactly(&self.encoding.next, next_tuples)
        //     .expect("Failed to bind next");

        let head_tuples = self.encoding.copy_from(&t, cex.tuples(&checker.encoding.head).expect("head tuples"));
        eprintln!("  head: {} tuples", head_tuples.size());
        b.bound_exactly(&self.encoding.head, head_tuples)
            .expect("Failed to bind head");

        let data_tuples = self.encoding.copy_from(&t, cex.tuples(&checker.encoding.data).expect("data tuples"));
        eprintln!("  data: {} tuples", data_tuples.size());
        b.bound_exactly(&self.encoding.data, data_tuples)
            .expect("Failed to bind data");

        let this_list_tuples = self.encoding.copy_from(&t, cex.tuples(&checker.encoding.this_list).expect("this_list tuples"));
        eprintln!("  this_list: {} tuples", this_list_tuples.size());
        b.bound_exactly(&self.encoding.this_list, this_list_tuples)
            .expect("Failed to bind this_list");

        b
    }

    fn synth(&self, size: usize) -> Solution {
        eprintln!("\n>>> ENTERING synth() <<<");
        let formula = self.synth_spec();
        eprintln!(">>> Formula created <<<");

        let bounds = self.synth_bounds(size);
        eprintln!(">>> Bounds created <<<");

        eprintln!("DEBUG: Checking bounds for synthesis:");
        eprintln!("  Universe size: {}", bounds.universe().size());
        eprintln!("  Number of relations: {}", bounds.relations().count());

        // Check if hole is bounded
        if let Some(lower) = bounds.lower_bound(&self.hole) {
            eprintln!("  hole lower bound: {} tuples", lower.size());
        }
        if let Some(upper) = bounds.upper_bound(&self.hole) {
            eprintln!("  hole upper bound: {} tuples", upper.size());
        }

        eprintln!(">>> Calling solver.solve() <<<");
        let options = Options::default();
        let solver = Solver::new(options);
        let result = solver.solve(&formula, &bounds)
            .expect("Failed to solve");
        eprintln!(">>> Solver returned <<<");
        result
    }

    fn show_synth(&self, size: usize) {
        println!("************ SYNTHESIZE REVERSE REPAIR FOR {size} NODES ************");

        // First run the checker to get a counterexample
        let checker = ListCheck::new();
        eprintln!("Running checker...");
        let check_sol = checker.check(size);
        eprintln!("Checker done: {:?}", match &check_sol {
            Solution::Sat { .. } => "SAT",
            Solution::Unsat { .. } => "UNSAT",
            _ => "OTHER"
        });

        let sol = self.synth(size);
        let outcome = match &sol {
            Solution::Sat { .. } => "SATISFIABLE (synthesis found)",
            Solution::Unsat { .. } => "UNSATISFIABLE (no synthesis)",
            Solution::Trivial { is_true, .. } => {
                if *is_true {
                    "TRIVIALLY TRUE"
                } else {
                    "TRIVIALLY FALSE"
                }
            }
        };
        println!("{outcome}");
        println!();
        println!("{:?}", sol.statistics());
        println!();

        // Print the synthesized hole value
        if let Solution::Sat { ref instance, .. } = sol {
            println!("\n-----------Syntax-----------");
            if let Some(hole_tuples) = instance.tuples(&self.hole) {
                println!("\"??\" = {hole_tuples:?}");
            }
        }

        // TODO: Add visualization support via ListViz
        // ListViz::print_instance(self, sol.instance());
        // ListViz::print_state_graph("synth-pre", self, sol.instance(), State::PRE);
        // ListViz::print_state_graph("synth-post", self, sol.instance(), State::POST);
    }
}

fn main() {
    let enc = ListSynth::new();
    enc.show_synth(3);
}
