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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR IN CONNECTION WITH
 * THE SOFTWARE.
 */

//! Evaluator for relational formulas and expressions
//!
//! Following Java: kodkod.engine.Evaluator

use crate::ast::{Expression, Formula, IntExpression};
use crate::bool::Options;
use crate::instance::{Instance, TupleSet};
use crate::translator::Translator;

/// An evaluator for relational formulas and expressions with
/// respect to a given Instance and Options.
///
/// Following Java: kodkod.engine.Evaluator
pub struct Evaluator<'a> {
    instance: &'a Instance,
    options: Options,
}

impl<'a> Evaluator<'a> {
    /// Constructs a new Evaluator for the given instance, using default Options
    /// Following Java: Evaluator(Instance)
    pub fn new(instance: &'a Instance) -> Self {
        Self {
            instance,
            options: Options::default(),
        }
    }

    /// Constructs a new Evaluator for the given instance and options
    /// Following Java: Evaluator(Instance, Options)
    pub fn with_options(instance: &'a Instance, options: Options) -> Self {
        Self { instance, options }
    }

    /// Returns the Options object used by this evaluator
    /// Following Java: Evaluator.options()
    pub fn options(&self) -> &Options {
        &self.options
    }

    /// Returns the instance
    /// Following Java: Evaluator.instance()
    pub fn instance(&self) -> &Instance {
        self.instance
    }

    /// Evaluates the specified formula with respect to the instance
    /// Following Java: Evaluator.evaluate(Formula)
    ///
    /// Returns true if formula is true with respect to the instance; otherwise returns false
    pub fn evaluate(&self, formula: &Formula) -> bool {
        Translator::evaluate_formula(formula, self.instance, &self.options)
    }

    /// Evaluates the specified expression with respect to the instance
    /// Following Java: Evaluator.evaluate(Expression)
    ///
    /// Returns the set of tuples to which the expression evaluates
    pub fn evaluate_expression(&self, expression: &Expression) -> TupleSet {
        let indices = Translator::evaluate_expression(expression, self.instance, &self.options);
        let factory = self.instance.universe().factory();
        factory.set_of(expression.arity(), &indices)
    }

    /// Evaluates the specified int expression with respect to the instance
    /// Following Java: Evaluator.evaluate(IntExpression)
    ///
    /// Returns the integer to which the expression evaluates
    pub fn evaluate_int_expression(&self, int_expr: &IntExpression) -> i32 {
        Translator::evaluate_int_expression(int_expr, self.instance, &self.options)
    }
}
