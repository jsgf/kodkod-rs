//! LeafInterpreter for converting relations and constants to BooleanMatrices
//!
//! Following Java: kodkod.engine.fol2sat.LeafInterpreter

use crate::ast::{ConstantExpr, Relation};
use crate::bool::{
    BooleanFactory, BooleanMatrix, Dimensions, Options,
    VariableAllocator,
};
use crate::instance::{Bounds, Instance, TupleSet, Universe};
use rustc_hash::FxHashMap;
use std::ops::Range;

/// Interprets leaf expressions (Relations, Constants) as BooleanMatrices
///
/// Following Java: LeafInterpreter
pub struct LeafInterpreter {
    factory: BooleanFactory,
    universe: Universe,
    var_ranges: FxHashMap<Relation, Range<u32>>,
    lower_bounds: FxHashMap<Relation, TupleSet>,
    upper_bounds: FxHashMap<Relation, TupleSet>,
    int_bounds: FxHashMap<i32, TupleSet>,
}

impl LeafInterpreter {
    /// Creates a LeafInterpreter from Bounds, allocating variables for all relations
    /// Following Java: LeafInterpreter constructor
    pub fn from_bounds(bounds: &Bounds, options: &Options) -> Self {
        let mut allocator = VariableAllocator::new();
        let mut var_ranges = FxHashMap::default();
        let mut lower_bounds = FxHashMap::default();
        let mut upper_bounds = FxHashMap::default();

        // Collect bounds and allocate variables for each relation
        for relation in bounds.relations() {
            let lower = bounds.lower_bound(relation).unwrap();
            let upper = bounds.upper_bound(relation).unwrap();

            let range = allocator.allocate_for_relation(relation, lower.size(), upper.size());

            if !range.is_empty() {
                var_ranges.insert(relation.clone(), range);
            }

            lower_bounds.insert(relation.clone(), lower.clone());
            upper_bounds.insert(relation.clone(), upper.clone());
        }

        // Collect integer bounds
        let mut int_bounds = FxHashMap::default();
        for i in bounds.int_keys() {
            if let Some(tuple_set) = bounds.int_bound(i) {
                int_bounds.insert(i, tuple_set.clone());
            }
        }

        // Create factory with total allocated variables
        let factory = BooleanFactory::new(allocator.total_variables(), options.clone());

        Self {
            factory,
            universe: bounds.universe().clone(),
            var_ranges,
            lower_bounds,
            upper_bounds,
            int_bounds,
        }
    }

    /// Creates a LeafInterpreter from an Instance for evaluation
    /// Following Java: LeafInterpreter.exact(Instance, Options)
    ///
    /// When evaluating against an instance, all relations are bound exactly
    /// (lower = upper = the tuples in the instance), so no variables are needed.
    pub fn from_instance(instance: &Instance, options: &Options) -> Self {
        let relation_tuples = instance.relation_tuples();

        // For exact interpretation, lower = upper = instance tuples
        // No variables needed since everything is determined
        let lower_bounds = relation_tuples.clone();
        let upper_bounds = relation_tuples.clone();
        let var_ranges = FxHashMap::default(); // No variables
        let int_bounds = FxHashMap::default(); // TODO: support when needed

        // Create factory with 0 variables (all constants)
        let factory = BooleanFactory::new(0, options.clone());

        Self {
            factory,
            universe: instance.universe().clone(),
            var_ranges,
            lower_bounds,
            upper_bounds,
            int_bounds,
        }
    }

    /// Returns a reference to the factory (has interior mutability)
    pub fn factory(&self) -> &BooleanFactory {
        &self.factory
    }

    /// Returns a reference to the universe
    pub fn universe(&self) -> &Universe {
        &self.universe
    }

    /// Returns the number of primary variables (relation encoding variables)
    /// These are the variables that encode tuple membership in relations,
    /// as opposed to auxiliary Tseitin variables for gate encoding.
    pub fn num_primary_variables(&self) -> u32 {
        self.factory.num_variables()
    }

    /// Returns the variable ranges for all relations
    /// Used for solution extraction from SAT model
    pub fn variable_ranges(&self) -> &FxHashMap<Relation, Range<u32>> {
        &self.var_ranges
    }

    /// Returns the lower bounds for all relations
    /// Used for solution extraction
    pub fn lower_bounds(&self) -> &FxHashMap<Relation, TupleSet> {
        &self.lower_bounds
    }

    /// Returns the upper bounds for all relations
    /// Used for solution extraction
    pub fn upper_bounds(&self) -> &FxHashMap<Relation, TupleSet> {
        &self.upper_bounds
    }

    /// Interprets a relation as a BooleanMatrix
    /// Following Java: LeafInterpreter.interpret(Relation)
    pub fn interpret_relation(&self, rel: &Relation) -> BooleanMatrix {
        let lower = self
            .lower_bounds
            .get(rel)
            .expect("Relation not in bounds");
        let upper = self
            .upper_bounds
            .get(rel)
            .expect("Relation not in bounds");

        // Convert tuples to flat indices
        let lower_indices = Self::tuple_set_to_indices(lower);
        let upper_indices = Self::tuple_set_to_indices(upper);

        // Create matrix: upper indices define domain, lower indices are TRUE
        let dims = Dimensions::new(
            self.universe.size().pow(rel.arity() as u32),
            rel.arity(),
        );

        let mut matrix =
            BooleanMatrix::with_bounds(dims, &self.factory, &upper_indices, &lower_indices);

        // Assign variables to tuples in (upper - lower)
        if let Some(var_range) = self.var_ranges.get(rel) {
            let mut var_id = var_range.start;

            for &idx in &upper_indices {
                if !lower_indices.contains(&idx) {
                    // This tuple is uncertain - assign a variable
                    matrix.set(idx, self.factory.variable(var_id as i32));
                    var_id += 1;
                }
            }
        }

        matrix
    }

    /// Interprets a constant expression (UNIV, NONE, IDEN, INTS)
    /// Following Java: LeafInterpreter.interpret(ConstantExpression)
    pub fn interpret_constant(&self, c: ConstantExpr) -> BooleanMatrix {
        let univ_size = self.universe.size();

        match c {
            ConstantExpr::Univ => {
                // All unary tuples
                let dims = Dimensions::new(univ_size, 1);
                let all_indices: Vec<usize> = (0..univ_size).collect();
                BooleanMatrix::with_bounds(
                    dims,
                    &self.factory,
                    &all_indices,
                    &all_indices, // All TRUE
                )
            }

            ConstantExpr::None => {
                // Empty set
                let dims = Dimensions::new(univ_size, 1);
                BooleanMatrix::with_bounds(
                    dims,
                    &self.factory,
                    &[], // No indices
                    &[],
                )
            }

            ConstantExpr::Iden => {
                // Identity: {(i,i) | i in universe}
                // Binary relation, so capacity = univ_size²
                let dims = Dimensions::new(univ_size * univ_size, 2);
                let mut iden_indices = Vec::new();
                for i in 0..univ_size {
                    iden_indices.push(i * univ_size + i);
                }
                BooleanMatrix::with_bounds(
                    dims,
                    &self.factory,
                    &iden_indices,
                    &iden_indices, // All TRUE
                )
            }

            ConstantExpr::Ints => {
                // Following Java: LeafInterpreter.interpret(ConstantExpression)
                // Returns the set of all integers with bounds
                let dims = Dimensions::new(univ_size, 1);
                let mut indices = Vec::new();
                for i in self.ints() {
                    indices.push(self.interpret(i));
                }
                BooleanMatrix::with_bounds(dims, &self.factory, &indices, &indices)
            }
        }
    }

    /// Returns the set of integers with bounds
    /// Following Java: LeafInterpreter.ints()
    pub fn ints(&self) -> impl Iterator<Item = i32> + '_ {
        self.int_bounds.keys().copied()
    }

    /// Returns the index of the atom from this.universe which represents the given integer
    /// Following Java: LeafInterpreter.interpret(int)
    /// @requires i in this.ints
    /// @return this.ibounds[i].indexView().min()
    pub fn interpret(&self, i: i32) -> usize {
        let tuple_set = self.int_bounds.get(&i).expect("Integer not in bounds");
        assert_eq!(tuple_set.arity(), 1, "Integer tuple set must be unary");
        assert_eq!(tuple_set.size(), 1, "Integer tuple set must be singleton");
        // Return the index of the first (and only) tuple
        tuple_set.iter().next().unwrap().index()
    }

    /// Converts a TupleSet to flat indices for BooleanMatrix
    /// Following Java pattern from LeafInterpreter
    pub fn tuple_set_to_indices(tuple_set: &TupleSet) -> Vec<usize> {
        let mut indices = Vec::new();

        for tuple in tuple_set.iter() {
            // Use the stored index from the tuple
            indices.push(tuple.index());
        }

        indices
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Relation;
    use crate::bool::BooleanConstant;
    use crate::instance::{Bounds, Universe};

    #[test]
    fn test_leaf_interpreter_creation() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let _interpreter = LeafInterpreter::from_bounds(&bounds, &options);
    }

    #[test]
    fn test_interpret_constant_univ() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let matrix = interpreter.interpret_constant(ConstantExpr::Univ);
        assert_eq!(matrix.dimensions().capacity(), 3);
        assert_eq!(matrix.density(), 3); // All TRUE
    }

    #[test]
    fn test_interpret_constant_none() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let matrix = interpreter.interpret_constant(ConstantExpr::None);
        assert_eq!(matrix.density(), 0); // All FALSE (sparse)
    }

    #[test]
    fn test_interpret_constant_iden() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let matrix = interpreter.interpret_constant(ConstantExpr::Iden);
        assert_eq!(matrix.dimensions().capacity(), 4); // 2x2
        assert_eq!(matrix.density(), 2); // Only diagonal: (A,A) and (B,B)

        // Check diagonal is TRUE
        assert_eq!(matrix.get(0).label(), BooleanConstant::TRUE.label()); // (A,A) at index 0
        assert_eq!(matrix.get(3).label(), BooleanConstant::TRUE.label()); // (B,B) at index 3
        // Off-diagonal should be FALSE
        assert_eq!(matrix.get(1).label(), BooleanConstant::FALSE.label());
        assert_eq!(matrix.get(2).label(), BooleanConstant::FALSE.label());
    }

    #[test]
    fn test_interpret_relation() {
        let universe = Universe::new(&["A", "B", "C"]).unwrap();
        let mut bounds = Bounds::new(universe.clone());

        let r = Relation::unary("R");
        let factory = bounds.universe().factory();

        // R: lower={(A)}, upper={(A), (B), (C)}
        bounds
            .bound(
                &r,
                factory.tuple_set(&[&["A"]]).unwrap(),
                factory.tuple_set(&[&["A"], &["B"], &["C"]]).unwrap(),
            )
            .unwrap();

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);
        let matrix = interpreter.interpret_relation(&r);

        // Index 0 (A) → TRUE (in lower bound)
        assert_eq!(matrix.get(0).label(), BooleanConstant::TRUE.label());

        // Index 1 (B) → variable 1 (uncertain)
        assert!(matrix.get(1).is_variable());
        assert_eq!(matrix.get(1).label(), 1);

        // Index 2 (C) → variable 2 (uncertain)
        assert!(matrix.get(2).is_variable());
        assert_eq!(matrix.get(2).label(), 2);
    }

    #[test]
    fn test_ints_iterator() {
        let universe = Universe::new(&["a", "b", "c", "d", "e"]).unwrap();
        let mut bounds = Bounds::new(universe.clone());

        // Bind integers -2, -1, 0, 1, 2 to atoms a, b, c, d, e
        let factory = bounds.universe().factory();
        let atoms = ["a", "b", "c", "d", "e"];
        for (idx, i) in (-2..=2).enumerate() {
            bounds.bound_exactly_int(i, factory.tuple_set(&[&[atoms[idx]]]).unwrap()).unwrap();
        }

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        let mut ints: Vec<i32> = interpreter.ints().collect();
        ints.sort(); // Order not guaranteed from hashmap

        assert_eq!(ints, vec![-2, -1, 0, 1, 2]);
    }

    #[test]
    fn test_interpret_integer() {
        let universe = Universe::new(&["a", "b", "c", "0", "1", "2"]).unwrap();
        let mut bounds = Bounds::new(universe.clone());

        // Bind integer 0 to atom "0" (index 3)
        // Bind integer 1 to atom "1" (index 4)
        // Bind integer 2 to atom "2" (index 5)
        let factory = bounds.universe().factory();
        bounds.bound_exactly_int(0, factory.tuple_set(&[&["0"]]).unwrap()).unwrap();
        bounds.bound_exactly_int(1, factory.tuple_set(&[&["1"]]).unwrap()).unwrap();
        bounds.bound_exactly_int(2, factory.tuple_set(&[&["2"]]).unwrap()).unwrap();

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        // interpret(0) should return index 3
        assert_eq!(interpreter.interpret(0), 3);
        // interpret(1) should return index 4
        assert_eq!(interpreter.interpret(1), 4);
        // interpret(2) should return index 5
        assert_eq!(interpreter.interpret(2), 5);
    }

    #[test]
    #[should_panic(expected = "Integer not in bounds")]
    fn test_interpret_unbounded_integer() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        // Should panic - no integers bounded
        interpreter.interpret(42);
    }

    #[test]
    fn test_integer_bounds_empty() {
        let universe = Universe::new(&["A", "B"]).unwrap();
        let bounds = Bounds::new(universe.clone());

        let options = Options::default();
        let interpreter = LeafInterpreter::from_bounds(&bounds, &options);

        // No integers should be present
        assert_eq!(interpreter.ints().count(), 0);
    }
}
