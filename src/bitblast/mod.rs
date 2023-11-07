use std::ffi::CStr;
use std::ops::{Add, BitAnd, BitOr, BitXor, Neg, Not, Sub};

use crate::global_z3::Bool;

pub struct U32 {
    bits: Box<[Bool; 32]>,
}

impl U32 {
    pub fn new(name: &str) -> Self {
        let bits = (0..32)
            .map(|i| {
                let s = format!("{name}_{i}\0");
                Bool::new(CStr::from_bytes_with_nul(s.as_bytes()).unwrap())
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        U32 { bits }
    }

    fn from_op(mut op: impl FnMut(usize) -> Bool) -> Self {
        macro_rules! bits[($($bit:expr,)*) => {
            Box::new([$(op($bit)),*])
        }];
        U32::from(bits![
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31,
        ])
    }

    pub fn inc(&self) -> U32 {
        U32::from(inc32(&self.bits[..]))
    }
}

impl From<u32> for U32 {
    fn from(n: u32) -> Self {
        macro_rules! bits[($($bit:expr,)*) => {
            Box::new([$(Bool::from((n >> $bit) & 1 == 1)),*])
        }];
        U32::from(bits![
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31,
        ])
    }
}

impl From<Box<[Bool; 32]>> for U32 {
    #[inline]
    fn from(bits: Box<[Bool; 32]>) -> Self {
        U32 { bits }
    }
}

impl BitAnd for &U32 {
    type Output = U32;

    fn bitand(self, rhs: Self) -> Self::Output {
        U32::from_op(|i| self.bits[i].and(&rhs.bits[i]))
    }
}

impl BitOr for &U32 {
    type Output = U32;

    fn bitor(self, rhs: Self) -> Self::Output {
        U32::from_op(|i| self.bits[i].or(&rhs.bits[i]))
    }
}

impl BitXor for &U32 {
    type Output = U32;

    fn bitxor(self, rhs: Self) -> Self::Output {
        U32::from_op(|i| self.bits[i].xor(&rhs.bits[i]))
    }
}

impl Add for &U32 {
    type Output = U32;

    fn add(self, rhs: Self) -> Self::Output {
        U32::from(add32(&self.bits[..], &rhs.bits[..]))
    }
}

impl Sub for &U32 {
    type Output = U32;

    fn sub(self, rhs: Self) -> Self::Output {
        self + &-rhs
    }
}

impl Not for &U32 {
    type Output = U32;

    fn not(self) -> Self::Output {
        U32::from_op(|i| !&self.bits[i])
    }
}

impl Neg for &U32 {
    type Output = U32;

    fn neg(self) -> Self::Output {
        (!self).inc()
    }
}

#[inline]
fn add1(x: &Bool, y: &Bool, c: &Bool, z: &mut Vec<Bool>) -> Bool {
    let xy = &(x ^ y);
    z.push(xy ^ c);
    (xy & c) | (x & y)
}
#[inline]
fn add8(x: &[Bool], y: &[Bool], mut c: Bool, z: &mut Vec<Bool>) -> Bool {
    c = add1(&x[0], &y[0], &c, z);
    c = add1(&x[1], &y[1], &c, z);
    c = add1(&x[2], &y[2], &c, z);
    c = add1(&x[3], &y[3], &c, z);
    c = add1(&x[4], &y[4], &c, z);
    c = add1(&x[5], &y[5], &c, z);
    c = add1(&x[6], &y[6], &c, z);
    c = add1(&x[7], &y[7], &c, z);
    c
}
#[inline]
fn add32(x: &[Bool], y: &[Bool]) -> Box<[Bool; 32]> {
    let mut z = Vec::with_capacity(32);
    let mut c;
    c = add8(&x[..8], &y[..8], Bool::from(false), &mut z);
    c = add8(&x[8..16], &y[8..16], c, &mut z);
    c = add8(&x[16..24], &y[16..24], c, &mut z);
    _ = add8(&x[24..], &y[24..], c, &mut z);
    z.try_into().unwrap()
}

#[inline]
fn inc1(x: &Bool, c: &Bool, z: &mut Vec<Bool>) -> Bool {
    z.push(x ^ c);
    x & c
}
#[inline]
fn inc8(x: &[Bool], mut c: Bool, z: &mut Vec<Bool>) -> Bool {
    c = inc1(&x[0], &c, z);
    c = inc1(&x[1], &c, z);
    c = inc1(&x[2], &c, z);
    c = inc1(&x[3], &c, z);
    c = inc1(&x[4], &c, z);
    c = inc1(&x[5], &c, z);
    c = inc1(&x[6], &c, z);
    c = inc1(&x[7], &c, z);
    c
}
#[inline]
fn inc32(x: &[Bool]) -> Box<[Bool; 32]> {
    let mut z = Vec::with_capacity(32);
    let mut c;
    c = inc8(&x[..8], Bool::from(true), &mut z);
    c = inc8(&x[8..16], c, &mut z);
    c = inc8(&x[16..24], c, &mut z);
    _ = inc8(&x[24..], c, &mut z);
    z.try_into().unwrap()
}
