//! Integer representation as bit-vector circuits
//!
//! Following Java: kodkod.engine.bool.Int and TwosComplementInt
//! Represents integers using bit-vectors in two's complement form.
//! Bits are stored in little-endian order (LSB first).

use crate::bool::{BoolValue, BooleanConstant, BooleanFactory};

/// Represents an integer using boolean values (bits) in two's complement form.
/// Each bit can be a boolean variable or constant.
/// Bits are indexed from 0 (LSB) to width-1 (sign bit).
#[derive(Clone, Debug)]
pub struct Int {
    bits: Vec<BoolValue>,
}

impl Int {
    /// Creates a new Int with the given bits
    /// bits[0] is LSB, bits[width-1] is sign bit (two's complement)
    pub fn new(bits: Vec<BoolValue>) -> Self {
        assert!(!bits.is_empty(), "Int must have at least one bit");
        Self { bits }
    }

    /// Creates an Int from a constant integer value with given bitwidth
    /// The bits are represented using the given boolean value for 1-bits
    /// and FALSE for 0-bits, except the sign bit uses the given value or FALSE
    pub fn constant(value: i32, bitwidth: usize, one_bit: BoolValue) -> Self {
        let mut bits = Vec::with_capacity(bitwidth);

        for i in 0..bitwidth {
            let bit_is_set = if i < 31 {
                (value & (1 << i)) != 0
            } else if i == 31 {
                value < 0
            } else {
                false
            };

            bits.push(if bit_is_set {
                one_bit.clone()
            } else {
                BoolValue::Constant(BooleanConstant::FALSE)
            });
        }

        Self { bits }
    }

    /// Returns the number of bits
    pub fn width(&self) -> usize {
        self.bits.len()
    }

    /// Returns the bit at the given index (LSB = 0)
    pub fn bit(&self, i: usize) -> BoolValue {
        if i < self.bits.len() {
            self.bits[i].clone()
        } else {
            // Sign-extend: return the sign bit
            self.bits[self.bits.len() - 1].clone()
        }
    }

    /// Returns true if all bits are constants
    pub fn is_constant(&self) -> bool {
        self.bits.iter().all(|b| matches!(b, BoolValue::Constant(_)))
    }

    /// If constant, returns the value
    pub fn value(&self) -> Option<i32> {
        if !self.is_constant() {
            return None;
        }

        let mut result = 0i32;
        for (i, bit) in self.bits.iter().enumerate() {
            if let BoolValue::Constant(c) = bit {
                let is_true = *c == BooleanConstant::TRUE;
                if i < 31 {
                    if is_true {
                        result |= 1 << i;
                    }
                } else if i == 31 {
                    // Sign bit
                    if is_true {
                        result |= 1i32 << 31;
                    }
                }
            }
        }
        Some(result)
    }

    /// Returns a boolean circuit encoding the equality comparison
    /// Follows Java: TwosComplementInt.eq()
    pub fn eq(&self, other: &Int, factory: &mut BooleanFactory) -> BoolValue {
        let width = self.width().max(other.width());
        let mut comparisons = Vec::new();

        for i in 0..width {
            let a = self.bit(i);
            let b = other.bit(i);
            // a == b iff factory.iff(a, b)
            let cmp = factory.iff(a, b);
            if cmp == BoolValue::Constant(BooleanConstant::FALSE) {
                return BoolValue::Constant(BooleanConstant::FALSE);
            }
            comparisons.push(cmp);
        }

        factory.and_multi(comparisons)
    }

    /// Returns a boolean circuit encoding the less-than-or-equal comparison
    /// Follows Java: TwosComplementInt.lte()
    /// Uses ripple comparator starting from MSB
    pub fn lte(&self, other: &Int, factory: &mut BooleanFactory) -> BoolValue {
        let width = self.width().max(other.width());
        if width == 0 {
            return BoolValue::Constant(BooleanConstant::TRUE);
        }

        let last = width - 1;
        let mut constraints = Vec::new();

        // Start with sign bit: other.sign_bit => this.sign_bit
        // (if other is negative, this must be negative)
        constraints.push(factory.implies(other.bit(last).clone(), self.bit(last).clone()));

        // prevEquals: bits[last] of both are equal
        let mut prev_equals = factory.iff(self.bit(last), other.bit(last));

        // Work from MSB-1 down to LSB
        for i in (0..last).rev() {
            let v0 = self.bit(i);
            let v1 = other.bit(i);

            // If prevEquals, then (this[i] <= other[i])
            // Which is: prevEquals => (this[i] => other[i])
            let v0_implies_v1 = factory.implies(v0.clone(), v1.clone());
            constraints.push(factory.implies(prev_equals.clone(), v0_implies_v1));

            // Update prevEquals: still equal if this[i] == other[i]
            prev_equals = factory.and(prev_equals, factory.iff(v0, v1));
        }

        factory.and_multi(constraints)
    }

    /// Returns a boolean circuit encoding the less-than comparison
    /// Follows Java: TwosComplementInt.lt()
    /// a < b iff (a <= b) and (a != b)
    pub fn lt(&self, other: &Int, factory: &mut BooleanFactory) -> BoolValue {
        let leq = self.lte(other, factory);
        let eq = self.eq(other, factory);
        let not_eq = factory.not(eq);
        factory.and(leq, not_eq)
    }

    /// Returns a boolean circuit encoding the addition
    /// Follows Java: TwosComplementInt.plus()
    pub fn plus(&self, other: &Int, factory: &mut BooleanFactory) -> Int {
        let width = (self.width().max(other.width()) + 1).min(factory.bitwidth());
        let mut result_bits = Vec::with_capacity(width);
        let mut carry = BoolValue::Constant(BooleanConstant::FALSE);

        for i in 0..width {
            let v0 = self.bit(i);
            let v1 = other.bit(i);

            // Full adder: sum = v0 XOR v1 XOR carry
            let sum = factory.sum(v0.clone(), v1.clone(), carry.clone());
            result_bits.push(sum);

            // New carry
            carry = factory.carry(v0, v1, carry);
        }

        Int::new(result_bits)
    }

    /// Returns a boolean circuit encoding the subtraction
    /// Follows Java: TwosComplementInt.minus()
    /// a - b = a + (-b) = a + (~b + 1)
    pub fn minus(&self, other: &Int, factory: &mut BooleanFactory) -> Int {
        let width = (self.width().max(other.width()) + 1).min(factory.bitwidth());
        let mut result_bits = Vec::with_capacity(width);
        let mut carry = BoolValue::Constant(BooleanConstant::TRUE); // Start with 1 for two's complement

        for i in 0..width {
            let v0 = self.bit(i);
            let v1_neg = factory.not(other.bit(i)); // Negate (one's complement)

            // Full adder with negated v1
            let sum = factory.sum(v0.clone(), v1_neg.clone(), carry.clone());
            result_bits.push(sum);

            // New carry
            carry = factory.carry(v0, v1_neg, carry);
        }

        Int::new(result_bits)
    }

    /// Bitwise AND operation
    pub fn and(&self, other: &Int, factory: &mut BooleanFactory) -> Int {
        let width = self.width().max(other.width());
        let bits = (0..width)
            .map(|i| factory.and(self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Bitwise OR operation
    pub fn or(&self, other: &Int, factory: &mut BooleanFactory) -> Int {
        let width = self.width().max(other.width());
        let bits = (0..width)
            .map(|i| factory.or(self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Bitwise XOR operation
    pub fn xor(&self, other: &Int, factory: &mut BooleanFactory) -> Int {
        let width = self.width().max(other.width());
        let bits = (0..width)
            .map(|i| factory.xor(self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Bitwise NOT operation
    pub fn not(&self, factory: &mut BooleanFactory) -> Int {
        let bits = self.bits.iter()
            .map(|b| factory.not(b.clone()))
            .collect();
        Int::new(bits)
    }

    /// Left shift by a constant amount
    pub fn shift_left(&self, shift: usize, _factory: &mut BooleanFactory) -> Int {
        let width = self.width();
        let mut bits = Vec::with_capacity(width);

        for i in 0..width {
            if i < shift {
                bits.push(BoolValue::Constant(BooleanConstant::FALSE));
            } else {
                bits.push(self.bit(i - shift));
            }
        }

        Int::new(bits)
    }

    /// Right shift by a constant amount (zero extension)
    pub fn shift_right(&self, shift: usize, _factory: &mut BooleanFactory) -> Int {
        let width = self.width();
        let mut bits = Vec::with_capacity(width);

        for i in 0..width {
            if i + shift < width {
                bits.push(self.bit(i + shift));
            } else {
                bits.push(BoolValue::Constant(BooleanConstant::FALSE));
            }
        }

        Int::new(bits)
    }

    /// Arithmetic right shift (sign extension)
    pub fn shift_right_arithmetic(&self, shift: usize, _factory: &mut BooleanFactory) -> Int {
        let width = self.width();
        let sign_bit = self.bit(width - 1);
        let mut bits = Vec::with_capacity(width);

        for i in 0..width {
            if i + shift < width {
                bits.push(self.bit(i + shift));
            } else {
                bits.push(sign_bit.clone());
            }
        }

        Int::new(bits)
    }

    /// Absolute value
    pub fn abs(&self, factory: &mut BooleanFactory) -> Int {
        // If negative (sign bit set), negate; otherwise return as is
        let sign_bit = self.bit(self.width() - 1);
        let negated = self.negate(factory);

        // Use ite: if negative, use negated; else use self
        let mut result_bits = Vec::with_capacity(self.width());
        for i in 0..self.width() {
            let self_bit = self.bit(i);
            let neg_bit = negated.bit(i);
            // ite(sign_bit, neg_bit, self_bit)
            result_bits.push(factory.ite(sign_bit.clone(), neg_bit, self_bit));
        }

        Int::new(result_bits)
    }

    /// Negate (two's complement negation: ~x + 1)
    pub fn negate(&self, factory: &mut BooleanFactory) -> Int {
        let ones = self.not(factory);
        let one = Int::new(vec![BoolValue::Constant(BooleanConstant::TRUE)]);
        ones.plus(&one, factory)
    }

    /// Sign of the integer: -1 if negative, 0 if zero, 1 if positive
    pub fn sign(&self, factory: &mut BooleanFactory) -> Int {
        // Check if zero: all bits are FALSE
        let mut all_zero = vec![BoolValue::Constant(BooleanConstant::TRUE)];
        for bit in &self.bits {
            all_zero.push(factory.not(bit.clone()));
        }
        let is_zero = factory.and_multi(all_zero);

        // Sign bit determines negative
        let sign_bit = self.bit(self.width() - 1);

        let width = factory.bitwidth();

        // Result: [sign_bit, NOT(sign_bit) OR is_zero, is_zero]
        // -1 (negative): [1, 1, 0]
        //  0 (zero):     [0, 1, 0]
        //  1 (positive): [0, 0, 1]

        // Simplified:
        // bit[0] = NOT(is_zero) AND NOT(sign_bit)  (1 if positive)
        // bit[1] = is_zero  (1 if zero)
        // bit[2..] = sign_bit (1 if negative)

        // Actually, just use ite:
        // if is_zero: return 0
        // else if sign_bit: return -1 (all 1s with sign bit set)
        // else: return 1 (just bit 0 set)

        let zero = Int::new(vec![BoolValue::Constant(BooleanConstant::FALSE); width]);
        let one = Int::constant(1, width, BoolValue::Constant(BooleanConstant::TRUE));
        let neg_one = Int::constant(-1, width, BoolValue::Constant(BooleanConstant::TRUE));

        // if is_zero: 0, else if sign_bit: -1, else: 1
        let if_neg = factory.ite(sign_bit, neg_one.bits[0].clone(), one.bits[0].clone());
        let result = factory.ite(is_zero, zero.bits[0].clone(), if_neg);

        Int::new(vec![result])
    }
}
