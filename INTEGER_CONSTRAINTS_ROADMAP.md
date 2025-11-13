# Integer Constraint Implementation Roadmap

## Current Status
The Handshake example fails because integer constraints (like `p.shaken.count() != q.shaken.count()`) are not properly implemented. The current code returns `TRUE` (conservative approximation) for integer comparisons, which is incorrect.

## Root Cause
Java Kodkod represents integers as **bit-vector circuits** in the boolean layer, not as static values. Each integer is represented using multiple boolean variables (bits) in two's complement form, and operations like comparison generate proper boolean circuits that encode the comparison logic.

## Required Implementation

### 1. Integer Bit-Vector Type (`src/bool/int.rs`)
- `Int` struct: Represents an integer as a vector of boolean values (bits)
- **Methods**:
  - `new(bits: Vec<BoolValue>)` - Constructor
  - `width() -> usize` - Number of bits
  - `bit(i: usize) -> BoolValue` - Get bit at index
  - `is_constant() -> bool` - Check if all bits are constants
  - `value() -> Option<i32>` - Extract constant value if possible
  - `eq(&self, other: &Int) -> BoolValue` - Generate equality comparator circuit
  - `lt(&self, other: &Int) -> BoolValue` - Generate less-than comparator circuit
  - `lte(&self, other: &Int) -> BoolValue` - Generate less-than-or-equal circuit
  - `plus(&self, other: &Int) -> Int` - Generate adder circuit
  - `minus(&self, other: &Int) -> Int` - Generate subtractor circuit
  - `multiply(&self, other: &Int) -> Int` - Generate multiplier circuit
  - Bitwise operations: `and`, `or`, `xor`, `shl`, `shr`, `sha`
  - Unary operations: `negate`, `not`, `abs`, `sgn`

### 2. BooleanFactory Extensions
The `BooleanFactory` needs methods to generate arithmetic circuits:
- `add_full(a: BoolValue, b: BoolValue, cin: BoolValue) -> (BoolValue, BoolValue)` - Full adder
- `ripple_adder(a: &[BoolValue], b: &[BoolValue]) -> Vec<BoolValue>` - Multi-bit adder
- `ripple_comparator_lt(a: &[BoolValue], b: &[BoolValue]) -> BoolValue` - Comparator
- Methods for other operations (multiply, divide, etc.)

### 3. Translator Modifications (`src/translator.rs`)
- Change `translate_int_expr()` to return `Int` instead of `Option<i32>`
- For `Cardinality(expr)`: Count the density of the boolean matrix and create an `Int` representing that count
- For integer comparisons: Generate comparison circuits instead of trying static evaluation
- Properly bind integer variables in quantified formulas similar to expression variables

### 4. Integration Points
- `LeafInterpreter` needs to track integer variables
- `Environment` needs to store and lookup `Int` objects
- Formula translation for `IntComparison` needs to generate circuits using `Int::eq`, `Int::lt`, etc.

## Implementation Complexity

This is a substantial piece of work, comparable to the boolean circuit layer itself. Key challenges:

1. **Bit-width Management**: Need to track how many bits are needed for each integer based on bounds
2. **Circuit Generation**: Implementing efficient adders, comparators, multipliers as boolean circuits
3. **Two's Complement Semantics**: Proper sign handling and overflow behavior
4. **Integration**: Hooking this into the translation pipeline requires changes throughout the code

## Why This Matters

Without this implementation:
- Integer comparisons always evaluate conservatively (TRUE) or fail
- Constraints like "different people shook different numbers of hands" cannot be expressed properly
- The solver cannot generate correct CNF for problems involving integer counts or measurements

## Example: Handshake Fix

When translating `p.shaken.count() != q.shaken.count()`:

**Current (wrong)**:
- Evaluate counts at translation time → always returns TRUE or fails
- `p.shaken.count() != q.shaken.count()` becomes `TRUE != TRUE` = `FALSE`
- Formula becomes unsatisfiable

**Correct (needed)**:
- Create `Int` representing count of `p.shaken` (as boolean variables representing the count)
- Create `Int` representing count of `q.shaken`
- Generate comparator circuit using `Int::eq` to check if they're equal
- Negate the result to check if they're NOT equal
- This generates actual SAT clauses that the solver can work with

## Files to Create/Modify

1. Create: `src/bool/int.rs` - Integer type (~200-300 lines)
2. Create: `src/bool/circuits.rs` - Circuit generation helpers (~400-600 lines)
3. Modify: `src/bool/mod.rs` - Export new types
4. Modify: `src/bool/factory.rs` - Add circuit generation methods (~200-300 lines)
5. Modify: `src/translator.rs` - Use `Int` instead of `i32` in integer handling (~100-150 line changes)
6. Modify: `src/translator/environment.rs` - Track integer variables (~50 line changes)

## Estimated Effort

- Implementing properly: **2-3 full development sessions**
- Testing and debugging: **1-2 additional sessions**
- Total: **3-5 hours of focused work**

This is the correct implementation path - there are no shortcuts without compromising the solver's correctness.
