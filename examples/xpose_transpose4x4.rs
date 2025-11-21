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

//! Implements the transpose of a 4x4 matrix with shufps.

// these are the values that we will be synthesizing
const MX1: [usize; 4] = [9, 1, 4, 0];
const MX2: [usize; 4] = [12, 5, 10, 6];
const MI: [[usize; 4]; 4] = [[1, 2, 2, 3], [0, 2, 0, 3], [3, 0, 2, 3], [0, 2, 3, 0]];
const SX1: [usize; 4] = [9, 4, 12, 5];
const SX2: [usize; 4] = [7, 11, 0, 0];
const SI: [[usize; 4]; 4] = [[3, 0, 0, 3], [0, 2, 3, 0], [1, 3, 0, 2], [0, 3, 1, 3]];

/// Transposes a 4x4 matrix m given as an array of 16 values.
///
/// # Requirements
/// - m.length = 16
///
/// # Returns
/// some t: int[] |
///     t.length = 16 and
///     all i, j: [0..4] | t[4*i + j] = m[4*j + i]
fn transpose(m: &[i32; 16]) -> [i32; 16] {
    let mut t = [0; 16];
    for i in 0..4 {
        for j in 0..4 {
            t[4 * i + j] = m[4 * j + i];
        }
    }
    t
}

/// Transposes a 4x4 matrix m given as an array of 16 values, using
/// the shufps instruction.
///
/// # Requirements
/// - m.length = 16
///
/// # Returns
/// some t: int[] |
///     t.length = 16 and
///     all i, j: [0..4] | t[4*i + j] = m[4*j + i]
fn transpose_shufps(m: &[i32; 16]) -> [i32; 16] {
    let mut s = [0; 16];
    let mut t = [0; 16];

    write4(&mut s, 0, &shufps(&read4(m, MX1[0]), &read4(m, MX2[0]), &MI[0])); // s0
    write4(&mut s, 4, &shufps(&read4(m, MX1[1]), &read4(m, MX2[1]), &MI[1])); // s1
    write4(&mut s, 8, &shufps(&read4(m, MX1[2]), &read4(m, MX2[2]), &MI[2])); // s2
    write4(&mut s, 12, &shufps(&read4(m, MX1[3]), &read4(m, MX2[3]), &MI[3])); // s3

    write4(&mut t, 0, &shufps(&read4(&s, SX1[0]), &read4(&s, SX2[0]), &SI[0])); // t0
    write4(&mut t, 4, &shufps(&read4(&s, SX1[1]), &read4(&s, SX2[1]), &SI[1])); // t1
    write4(&mut t, 8, &shufps(&read4(&s, SX1[2]), &read4(&s, SX2[2]), &SI[2])); // t2
    write4(&mut t, 12, &shufps(&read4(&s, SX1[3]), &read4(&s, SX2[3]), &SI[3])); // t3

    assert_eq!(t, transpose(m));

    t
}

/// Simulates the shufps SIMD instruction.
///
/// # Requirements
/// - xmm1.length = 4 and xmm2.length = 4 and imm8.length = 4
/// - all i: [0..3] | 0 <= imm8[i] < 4
///
/// # Returns
/// 0->xmm1[imm8[0]] + 1->xmm1[imm8[1]] + 2->xmm2[imm8[2]] + 3->xmm2[imm8[3]]
fn shufps(xmm1: &[i32; 4], xmm2: &[i32; 4], imm8: &[usize; 4]) -> [i32; 4] {
    [xmm1[imm8[0]], xmm1[imm8[1]], xmm2[imm8[2]], xmm2[imm8[3]]]
}

/// Reads a subarray of length 4 from the given array, starting
/// at the given index.
///
/// # Requirements
/// - m.length >= 4
/// - pos >= 0 and pos + 4 <= m.length
///
/// # Returns
/// 0->m[pos] + 1->m[pos+1] + 2->[pos+2] + 3->[pos+3]
fn read4(m: &[i32], pos: usize) -> [i32; 4] {
    assert!(m.len() >= 4);
    assert!(pos + 4 <= m.len());
    [m[pos], m[pos + 1], m[pos + 2], m[pos + 3]]
}

/// Writes the four elements from the source into the destination array at the specified position.
///
/// # Requirements
/// - src.length = 4 and dst.length >= 4
/// - 0 <= pos <= dst.length - 4
///
/// # Ensures
/// dst = old(dst) ++ (pos->src[0] + (pos+1)->src[1] + (pos+2)->src[2] + (pos+3)->src[3])
fn write4(dst: &mut [i32], pos: usize, src: &[i32; 4]) {
    dst[pos] = src[0];
    dst[pos + 1] = src[1];
    dst[pos + 2] = src[2];
    dst[pos + 3] = src[3];
}

fn main() {
    let a = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    println!("a = {a:?}");
    println!("transpose(a) = {:?}", transpose(&a));
    println!("transposeShufps(a) = {:?}", transpose_shufps(&a));
}
