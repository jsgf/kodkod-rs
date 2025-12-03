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

//! Data structure repair demo.
//!
//! Following Java: kodkod.examples.bmc.ListRepair

use kodkod_rs::ast::{Expression, Formula, Relation};
use kodkod_rs::solver::{Solution, Solver, Options};
use kodkod_rs::instance::Bounds;

// Import the ListEncoding module and ListCheck
#[path = "bmc_list_encoding/mod.rs"]
mod bmc_list_encoding;

#[path = "bmc_list_check/mod.rs"]
mod bmc_list_check;

use bmc_list_encoding::ListEncoding;
use bmc_list_check::ListCheck;

struct ListRepair {
    encoding: ListEncoding,
    next3: Relation,
    head0: Relation,
}

impl ListRepair {
    fn new() -> Self {
        ListRepair {
            encoding: ListEncoding::new(),
            next3: Relation::binary("next3"),  // next3 = free variable
            head0: Relation::binary("head0"),  // head0 = free variable
        }
    }

    fn next3(&self) -> Expression {
        self.next3.clone().into()
    }

    fn head0(&self) -> Expression {
        self.head0.clone().into()
    }

    fn repair_spec(&self) -> Formula {
        Formula::and_all(vec![
            self.encoding.pre(),
            self.encoding.post_with(self.next3(), self.head0())
        ])
    }

    fn repair_bounds(&self, size: usize) -> Bounds {
        let mut b = self.encoding.bounds(size);
        let checker = ListCheck::new();
        let sol = checker.check(size);

        let cex = match sol {
            Solution::Sat { instance, .. } => instance,
            _ => panic!("Expected SAT solution from ListCheck"),
        };

        let t = b.universe().factory();

        // Set bounds for repair variables
        b.bound(&self.next3, t.none(2), b.upper_bound(&self.encoding.next).unwrap().clone())
            .expect("Failed to bound next3");
        b.bound(&self.head0, t.none(2), b.upper_bound(&self.encoding.head).unwrap().clone())
            .expect("Failed to bound head0");

        // Fix the counterexample values - use checker's relations since that's what's in the instance
        b.bound_exactly(&self.encoding.next, self.encoding.copy_from(&t, cex.tuples(&checker.encoding.next).expect("next tuples")))
            .expect("Failed to bind next");
        b.bound_exactly(&self.encoding.head, self.encoding.copy_from(&t, cex.tuples(&checker.encoding.head).expect("head tuples")))
            .expect("Failed to bind head");
        b.bound_exactly(&self.encoding.data, self.encoding.copy_from(&t, cex.tuples(&checker.encoding.data).expect("data tuples")))
            .expect("Failed to bind data");
        b.bound_exactly(&self.encoding.this_list, self.encoding.copy_from(&t, cex.tuples(&checker.encoding.this_list).expect("this_list tuples")))
            .expect("Failed to bind this_list");

        b
    }

    fn repair(&self, size: usize) -> Solution {
        let options = Options::default();
        let solver = Solver::new(options);
        solver.solve(&self.repair_spec(), &self.repair_bounds(size))
            .expect("Failed to solve")
    }

    fn show_repair(&self, size: usize) {
        let sol = self.repair(size);
        println!("************ REPAIR REVERSE FOR {size} NODES ************");
        let outcome = match &sol {
            Solution::Sat { .. } => "SATISFIABLE (repair found)",
            Solution::Unsat { .. } => "UNSATISFIABLE (no repair)",
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
        // TODO: Add visualization support via ListViz
        // ListViz::print_instance(&self.encoding, sol.instance());
        // ListViz::print_state_graph("repair-pre", &self.encoding, sol.instance(), State::PRE);
        // ListViz::print_state_graph("repair-post", &self.encoding, sol.instance(), State::POST);
    }
}

fn run() {
    let enc = ListRepair::new();
    enc.show_repair(3);
}

fn main() {
    run();
}

#[test]
fn test_bmc_list_repair_runs() {
    // Test that the example runs without panicking
    run();
}
