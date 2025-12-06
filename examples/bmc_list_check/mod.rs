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

#![allow(dead_code)]

// Bounded verification demo.
//
// Following Java: kodkod.examples.bmc.ListCheck

use kodkod_rs::ast::Formula;
use kodkod_rs::solver::{Solution, Solver, Options};
use kodkod_rs::instance::Bounds;

// Import the ListEncoding module
// Since Rust doesn't have inheritance, we'll use composition
#[path = "../bmc_list_encoding/mod.rs"]
mod bmc_list_encoding;

use bmc_list_encoding::ListEncoding;

pub struct ListCheck {
    pub encoding: ListEncoding,
}

impl ListCheck {
    pub fn new() -> Self {
        ListCheck {
            encoding: ListEncoding::new(),
        }
    }

    pub fn check_spec(&self) -> Formula {
        Formula::and_all(vec![
            self.encoding.pre(),
            self.encoding.loop_guard(),
            self.encoding.post().not(),
        ])
    }

    pub fn check_bounds(&self, size: usize) -> Bounds {
        self.encoding.bounds(size)
    }

    pub fn check(&self, size: usize) -> Solution {
        let options = Options::default();
        let solver = Solver::new(options);
        solver.solve(&self.check_spec(), &self.check_bounds(size))
            .expect("Failed to solve")
    }

    pub fn show_check(&self, size: usize) {
        let sol = self.check(size);
        println!("************ CHECK REVERSE FOR {size} NODES ************");
        let outcome = match &sol {
            Solution::Sat { .. } => "SATISFIABLE (bug found)",
            Solution::Unsat { .. } => "UNSATISFIABLE (no bug)",
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
        // ListViz::print_state_graph("check-pre", &self.encoding, sol.instance(), State::PRE);
        // ListViz::print_state_graph("check-post", &self.encoding, sol.instance(), State::POST);
    }
}
