//! Unit test for Variable AND Constant(TRUE) should return Variable

use kodkod_rs::bool::{BoolValue, BooleanConstant, BooleanFactory, BooleanVariable, Options};

#[test]
fn test_variable_and_true() {
    let factory = BooleanFactory::new(10, Options::default());

    let var = BoolValue::Variable(BooleanVariable::new(1));
    let true_const = BoolValue::Constant(BooleanConstant::TRUE);

    let result = factory.and(var.clone(), true_const);

    // Variable AND TRUE should equal Variable
    assert_eq!(result, var, "Variable AND TRUE should return the Variable");
}

#[test]
fn test_true_and_variable() {
    let factory = BooleanFactory::new(10, Options::default());

    let var = BoolValue::Variable(BooleanVariable::new(1));
    let true_const = BoolValue::Constant(BooleanConstant::TRUE);

    let result = factory.and(true_const, var.clone());

    // TRUE AND Variable should equal Variable
    assert_eq!(result, var, "TRUE AND Variable should return the Variable");
}
