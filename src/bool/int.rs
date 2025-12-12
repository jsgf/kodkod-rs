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
pub struct Int<'arena> {
    bits: Vec<BoolValue<'arena>>,
}

impl<'arena> Int<'arena> {
    /// Creates a new Int with the given bits
    /// bits[0] is LSB, bits[width-1] is sign bit (two's complement)
    pub fn new(bits: Vec<BoolValue<'arena>>) -> Self {
        assert!(!bits.is_empty(), "Int must have at least one bit");
        Self { bits }
    }

    /// Creates an Int from a constant integer value with given bitwidth
    /// The bits are represented using the given boolean value for 1-bits
    /// and FALSE for 0-bits, except the sign bit uses the given value or FALSE
    pub fn constant(value: i32, bitwidth: usize, one_bit: BoolValue<'arena>) -> Self {
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
    pub fn bit(&self, i: usize) -> BoolValue<'arena> {
        if i < self.bits.len() {
            self.bits[i].clone()
        } else {
            // Sign-extend: return the sign bit
            self.bits[self.bits.len() - 1].clone()
        }
    }

    /// Returns the two's complement bits
    /// Following Java: TwosComplementInt.twosComplementBits()
    pub fn twos_complement_bits(&self) -> &[BoolValue<'arena>] {
        &self.bits
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
        let width = self.bits.len();
        let sign_bit_index = width - 1;

        for (i, bit) in self.bits.iter().enumerate() {
            if let BoolValue::Constant(c) = bit {
                let is_true = *c == BooleanConstant::TRUE;
                if i == sign_bit_index {
                    // Sign bit - if set, this is negative
                    if is_true {
                        // Set all bits from sign_bit_index to 31 to handle sign extension
                        result |= (-1i32) << sign_bit_index;
                    }
                } else if is_true {
                    result |= 1 << i;
                }
            }
        }
        Some(result)
    }

    /// Returns a boolean circuit encoding the equality comparison
    /// Follows Java: TwosComplementInt.eq()
    pub fn eq(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        let width = self.width().max(other.width());
        let mut comparisons: Vec<BoolValue<'arena>> = Vec::new();

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
    pub fn lte(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        let width = self.width().max(other.width());
        if width == 0 {
            return BoolValue::Constant(BooleanConstant::TRUE);
        }

        let last = width - 1;
        let mut constraints: Vec<BoolValue<'arena>> = Vec::new();

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
    pub fn lt(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> BoolValue<'arena> {
        let leq = self.lte(other, factory);
        let eq = self.eq(other, factory);
        let not_eq = factory.not(eq);
        factory.and(leq, not_eq)
    }

    /// Conditional choice: returns this if condition is true, otherwise other
    /// Follows Java: TwosComplementInt.choice()
    /// Returns condition ? this : other
    pub fn choice(&self, condition: BoolValue<'arena>, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = self.width().max(other.width());
        let bits: Vec<BoolValue<'arena>> = (0..width)
            .map(|i| factory.ite(condition.clone(), self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Returns a boolean circuit encoding the addition
    /// Follows Java: TwosComplementInt.plus()
    pub fn plus(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = (self.width().max(other.width()) + 1).min(factory.bitwidth());
        let mut result_bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);
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
    pub fn minus(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = (self.width().max(other.width()) + 1).min(factory.bitwidth());
        let mut result_bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);
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
    pub fn and(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = self.width().max(other.width());
        let bits: Vec<BoolValue<'arena>> = (0..width)
            .map(|i| factory.and(self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Bitwise OR operation
    pub fn or(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = self.width().max(other.width());
        let bits: Vec<BoolValue<'arena>> = (0..width)
            .map(|i| factory.or(self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Bitwise XOR operation
    pub fn xor(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = self.width().max(other.width());
        let bits: Vec<BoolValue<'arena>> = (0..width)
            .map(|i| factory.xor(self.bit(i), other.bit(i)))
            .collect();
        Int::new(bits)
    }

    /// Bitwise NOT operation
    pub fn not(&self, factory: &'arena BooleanFactory) -> Int<'arena> {
        let bits: Vec<BoolValue<'arena>> = self.bits.iter()
            .map(|b| factory.not(b.clone()))
            .collect();
        Int::new(bits)
    }

    /// Left shift by a constant amount
    pub fn shift_left(&self, shift: usize) -> Int<'arena> {
        let width = self.width();
        let mut bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);

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
    pub fn shift_right(&self, shift: usize) -> Int<'arena> {
        let width = self.width();
        let mut bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);

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
    pub fn shift_right_arithmetic(&self, shift: usize) -> Int<'arena> {
        let width = self.width();
        let sign_bit = self.bit(width - 1);
        let mut bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);

        for i in 0..width {
            if i + shift < width {
                bits.push(self.bit(i + shift));
            } else {
                bits.push(sign_bit.clone());
            }
        }

        Int::new(bits)
    }

    /// Left shift by variable amount using barrel shifter
    /// Following Java: TwosComplementInt.shl()
    /// Uses cascaded conditional shifts based on each bit of the shift amount
    pub fn shl(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = factory.bitwidth();
        let mut shifted_bits = self.extend(width);

        // Barrel shifter: for each bit i in the shift amount, conditionally shift by 2^i
        for i in 0..width {
            let shift = 1usize << i; // 2^i
            let bit = other.bit(i);

            // Apply conditional shift
            for j in (0..width).rev() {
                let new_val = if j < shift {
                    BoolValue::Constant(BooleanConstant::FALSE)
                } else {
                    shifted_bits[j - shift].clone()
                };
                shifted_bits[j] = factory.ite(bit.clone(), new_val, shifted_bits[j].clone());
            }
        }

        Int::new(shifted_bits)
    }

    /// Right shift by variable amount with given fill value
    /// Helper for both logical (fill=FALSE) and arithmetic (fill=sign) shifts
    /// Following Java: TwosComplementInt.shr(Int, BooleanValue)
    fn shr_with_fill(&self, other: &Int<'arena>, factory: &'arena BooleanFactory, fill: BoolValue<'arena>) -> Int<'arena> {
        let width = factory.bitwidth();
        let mut shifted_bits = self.extend(width);

        // Barrel shifter: for each bit i in the shift amount, conditionally shift by 2^i
        for i in 0..width {
            let shift = 1usize << i; // 2^i
            let bit = other.bit(i);

            // Apply conditional shift
            for j in 0..width {
                let new_val = if j + shift < width {
                    shifted_bits[j + shift].clone()
                } else {
                    fill.clone()
                };
                shifted_bits[j] = factory.ite(bit.clone(), new_val, shifted_bits[j].clone());
            }
        }

        Int::new(shifted_bits)
    }

    /// Logical right shift by variable amount (zero extension)
    /// Following Java: TwosComplementInt.shr()
    pub fn shr(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        self.shr_with_fill(other, factory, BoolValue::Constant(BooleanConstant::FALSE))
    }

    /// Arithmetic right shift by variable amount (sign extension)
    /// Following Java: TwosComplementInt.sha()
    pub fn sha(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let sign_bit = self.bit(self.width() - 1);
        self.shr_with_fill(other, factory, sign_bit)
    }

    /// Absolute value
    pub fn abs(&self, factory: &'arena BooleanFactory) -> Int<'arena> {
        // Following Java: choice(factory.not(sign_bit), negate())
        // If positive (sign bit is 0), return self; otherwise return negated
        let sign_bit = self.bit(self.width() - 1);
        let not_sign = factory.not(sign_bit);
        let negated = self.negate(factory);

        // choice: if not_sign, use self; else use negated
        let width = self.width().max(negated.width());
        let mut result_bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);
        for i in 0..width {
            let self_bit = self.bit(i);
            let neg_bit = negated.bit(i);
            // ite(not_sign, self_bit, neg_bit)
            result_bits.push(factory.ite(not_sign.clone(), self_bit, neg_bit));
        }

        Int::new(result_bits)
    }

    /// Negate (two's complement negation: 0 - this)
    /// Following Java: TwosComplementInt.negate() = new Int([FALSE]).minus(this)
    pub fn negate(&self, factory: &'arena BooleanFactory) -> Int<'arena> {
        // Create 0 as a single-bit FALSE
        let zero = Int::new(vec![BoolValue::Constant(BooleanConstant::FALSE)]);
        zero.minus(self, factory)
    }

    /// Sign of the integer: -1 if negative, 0 if zero, 1 if positive
    /// Following Java: TwosComplementInt.sgn() returns 2-bit int:
    /// - bit[0] = OR of all bits (non-zero)
    /// - bit[1] = sign bit
    pub fn sign(&self, factory: &'arena BooleanFactory) -> Int<'arena> {
        // bit[0]: OR of all bits (true if non-zero)
        let bits_vec: Vec<BoolValue<'arena>> = self.bits.clone();
        let any_bit_set = if bits_vec.is_empty() {
            BoolValue::Constant(BooleanConstant::FALSE)
        } else {
            factory.or_multi(bits_vec)
        };

        // bit[1]: sign bit
        let sign_bit = self.bit(self.width() - 1);

        Int::new(vec![any_bit_set, sign_bit])
    }

    /// Multiplies this integer by another using partial sum circuit
    /// Following Java: TwosComplementInt.multiply()
    /// Uses Booth's algorithm for signed multiplication
    pub fn multiply(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let width = (self.width() + other.width()).min(factory.bitwidth());
        let mut mult_bits: Vec<BoolValue<'arena>> = Vec::with_capacity(width);

        // First partial sum: multiply bit(0) with all bits of other
        let i_bit = self.bit(0);
        for j in 0..width {
            mult_bits.push(factory.and(i_bit.clone(), other.bit(j)));
        }

        let last = width - 1;

        // Intermediate partial sums (for bits 1 to last-1)
        for i in 1..last {
            let mut carry = BoolValue::Constant(BooleanConstant::FALSE);
            let i_bit = self.bit(i);
            let jmax = width - i;

            for j in 0..jmax {
                let new_bit = factory.and(i_bit.clone(), other.bit(j));
                let index = j + i;

                // Add new_bit to mult_bits[index] with carry
                let old_bit = mult_bits[index].clone();
                mult_bits[index] = factory.sum(old_bit.clone(), new_bit.clone(), carry.clone());
                carry = factory.carry(old_bit, new_bit, carry);
            }
        }

        // Last partial sum is subtracted (sign bit handling for two's complement)
        // See http://en.wikipedia.org/wiki/Multiplication_ALU
        let last_bit = factory.and(self.bit(last), other.bit(0));
        let negated_last = factory.not(last_bit);
        let old_bit = mult_bits[last].clone();
        mult_bits[last] = factory.sum(
            old_bit.clone(),
            negated_last.clone(),
            BoolValue::Constant(BooleanConstant::TRUE)
        );

        Int::new(mult_bits)
    }

    /// Helper for division/modulo: extends this integer to the given width using sign extension
    /// Following Java: TwosComplementInt.extend()
    fn extend(&self, extwidth: usize) -> Vec<BoolValue<'arena>> {
        let mut ext = Vec::with_capacity(extwidth);
        let width = self.width();

        // Copy existing bits
        for i in 0..width {
            ext.push(self.bits[i].clone());
        }

        // Sign-extend
        let sign = self.bits[width - 1].clone();
        for _ in width..extwidth {
            ext.push(sign.clone());
        }

        ext
    }

    /// Performs non-restoring signed division
    /// Following Java: TwosComplementInt.nonRestoringDivision()
    /// Returns quotient if quotient=true, otherwise returns remainder
    /// See: Behrooz Parhami, Computer Arithmetic: Algorithms and Hardware Designs,
    /// Oxford University Press, 2000, pp. 218-221.
    fn non_restoring_division(&self, d: &Int<'arena>, factory: &'arena BooleanFactory, quotient: bool) -> Vec<BoolValue<'arena>> {
        let width = factory.bitwidth();
        let extended = width * 2 + 1;

        // Extend the dividend to bitwidth*2 + 1 and store in s
        let mut s = self.extend(extended);
        let mut q: Vec<BoolValue<'arena>> = Vec::with_capacity(width);

        // Detects if one of the intermediate remainders is zero
        let mut svalues: Vec<BoolValue<'arena>> = Vec::with_capacity(width);

        // The sign bit of the divisor
        let d_msb = d.bit(width);

        let mut sleft = 0; // Index containing LSB of s

        for _i in 0..width {
            // Collect OR of all s bits to detect zero
            svalues.push(factory.or_multi(s.clone()));

            let sright = (sleft + extended - 1) % extended; // Index containing MSB of s

            // q[width-i-1] is 1 if sign(s_i) = sign(d)
            let qbit = factory.iff(s[sright].clone(), d_msb.clone());
            q.push(qbit.clone());

            // Shift s to the left by 1 (simulated by setting sright to FALSE and sleft to sright)
            s[sright] = BoolValue::Constant(BooleanConstant::FALSE);
            sleft = sright;

            // If sign(s_i) = sign(d), subtract (2^width)d from s_i;
            // otherwise, add (2^width)d to s_i
            let mut carry = qbit.clone();
            for di in 0..=width {
                let si = (sleft + width + di) % extended;
                let dbit = factory.xor(qbit.clone(), d.bit(di));
                let sbit = s[si].clone();
                s[si] = factory.sum(sbit.clone(), dbit.clone(), carry.clone());
                carry = factory.carry(sbit, dbit, carry);
            }
        }

        // Reverse q since we built it backwards
        q.reverse();

        // Correction needed if one of the intermediate remainders is zero
        // or s is non-zero and its sign differs from the sign of the dividend
        let all_svalues_true = factory.and_multi(svalues);
        let not_all_svalues = factory.not(all_svalues_true);

        let s_nonzero = factory.or_multi(s[0..=width].to_vec());
        let s_sign_differs = factory.xor(s[width].clone(), self.bit(width));
        let sign_issue = factory.and(s_sign_differs, s_nonzero.clone());

        let incorrect = factory.or(not_all_svalues, sign_issue);
        let corrector = factory.iff(s[width].clone(), d.bit(width));

        if quotient {
            // Convert q to 2's complement: shift left by 1 and set LSB to TRUE
            let mut q_result = vec![BoolValue::Constant(BooleanConstant::TRUE)];
            q_result.extend_from_slice(&q[0..width-1]);

            // Correct if incorrect: if corrector is true, increment q; otherwise decrement q
            let sign = factory.and(incorrect.clone(), factory.not(corrector.clone()));
            let mut carry = factory.and(incorrect, corrector);

            for i in 0..width {
                let qbit = q_result[i].clone();
                q_result[i] = factory.sum(qbit.clone(), sign.clone(), carry.clone());
                carry = factory.carry(qbit, sign.clone(), carry);
            }

            q_result
        } else {
            // Correct s if incorrect: if corrector is true, subtract (2^width)d;
            // otherwise add (2^width)d
            let mut carry = factory.and(incorrect.clone(), corrector.clone());

            for i in 0..=width {
                let dbit = factory.and(
                    incorrect.clone(),
                    factory.xor(corrector.clone(), d.bit(i))
                );
                let sbit = s[i].clone();
                s[i] = factory.sum(sbit.clone(), dbit.clone(), carry.clone());
                carry = factory.carry(sbit, dbit, carry);
            }

            // Return width low-order bits
            s[0..width].to_vec()
        }
    }

    /// Divides this integer by another
    /// Following Java: TwosComplementInt.divide()
    pub fn divide(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let bits = self.non_restoring_division(other, factory, true);
        Int::new(bits)
    }

    /// Computes the modulo (remainder) of this integer divided by another
    /// Following Java: TwosComplementInt.modulo()
    pub fn modulo(&self, other: &Int<'arena>, factory: &'arena BooleanFactory) -> Int<'arena> {
        let bits = self.non_restoring_division(other, factory, false);
        Int::new(bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool::BooleanFactory;

    #[test]
    fn twos_complement_bits_access() {
        let _factory = BooleanFactory::new(0, crate::bool::Options::default());
        let int_val = Int::constant(5, 8, BoolValue::Constant(BooleanConstant::TRUE));

        let bits = int_val.twos_complement_bits();
        assert_eq!(bits.len(), 8);

        // 5 in binary is 00000101
        // bits[0] = LSB = 1
        // bits[1] = 0
        // bits[2] = 1
        // bits[3..7] = 0
        assert!(matches!(bits[0], BoolValue::Constant(BooleanConstant::TRUE)));
        assert!(matches!(bits[1], BoolValue::Constant(BooleanConstant::FALSE)));
        assert!(matches!(bits[2], BoolValue::Constant(BooleanConstant::TRUE)));
    }

    #[test]
    fn twos_complement_bits_negative() {
        let int_val = Int::constant(-1, 8, BoolValue::Constant(BooleanConstant::TRUE));

        let bits = int_val.twos_complement_bits();
        assert_eq!(bits.len(), 8);

        // -1 in two's complement is all 1s: 11111111
        for bit in bits {
            assert!(matches!(bit, BoolValue::Constant(BooleanConstant::TRUE)));
        }
    }

    #[test]
    fn int_constant_value() {
        let int_val = Int::constant(42, 8, BoolValue::Constant(BooleanConstant::TRUE));
        assert!(int_val.is_constant());
        assert_eq!(int_val.value(), Some(42));

        let int_neg = Int::constant(-10, 8, BoolValue::Constant(BooleanConstant::TRUE));
        assert!(int_neg.is_constant());
        assert_eq!(int_neg.value(), Some(-10));
    }

    #[test]
    fn int_eq_circuit() {
        let factory = BooleanFactory::new(10, crate::bool::Options::default());

        let a = Int::constant(5, 8, BoolValue::Constant(BooleanConstant::TRUE));
        let b = Int::constant(5, 8, BoolValue::Constant(BooleanConstant::TRUE));

        let eq = a.eq(&b, &factory);
        assert_eq!(eq, BoolValue::Constant(BooleanConstant::TRUE));

        let c = Int::constant(3, 8, BoolValue::Constant(BooleanConstant::TRUE));
        let neq = a.eq(&c, &factory);
        assert_eq!(neq, BoolValue::Constant(BooleanConstant::FALSE));
    }

    #[test]
    fn int_bit_access() {
        let int_val = Int::constant(10, 8, BoolValue::Constant(BooleanConstant::TRUE));

        // 10 in binary is 00001010
        // bit(0) = 0, bit(1) = 1, bit(2) = 0, bit(3) = 1
        assert!(matches!(int_val.bit(0), BoolValue::Constant(BooleanConstant::FALSE)));
        assert!(matches!(int_val.bit(1), BoolValue::Constant(BooleanConstant::TRUE)));
        assert!(matches!(int_val.bit(2), BoolValue::Constant(BooleanConstant::FALSE)));
        assert!(matches!(int_val.bit(3), BoolValue::Constant(BooleanConstant::TRUE)));
    }

    #[test]
    fn int_sign_extension() {
        let int_val = Int::constant(-1, 4, BoolValue::Constant(BooleanConstant::TRUE));

        // Sign bit should be extended when accessing beyond width
        let beyond_bit = int_val.bit(10);
        assert!(matches!(beyond_bit, BoolValue::Constant(BooleanConstant::TRUE)));
    }
}
