use std::ffi::CStr;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign,
    Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use std::{iter, usize};

use crate::global_z3::{Bool, Model};

#[derive(Clone, Debug)]
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

    pub fn equals(&self, rhs: &U32) -> Bool {
        Bool::all(
            self.bits
                .iter()
                .zip(rhs.bits.iter())
                .map(|(x, y)| x.equals(y)),
        )
    }

    pub fn ite(b_if: &Bool, v_then: &U32, v_else: &U32) -> U32 {
        U32::from_op(|i| Bool::ite(b_if, &v_then.bits[i], &v_else.bits[i]))
    }

    pub fn as_const(&self) -> Option<u32> {
        let mut v = 0u32;
        for (i, b) in self.bits.iter().enumerate() {
            v |= (b.as_const()? as u32) << i;
        }
        Some(v)
    }

    pub fn eval(&self, model: &Model, model_completion: bool) -> Option<U32> {
        self.bits
            .iter()
            .map(|bit| bit.eval(model, model_completion))
            .collect::<Option<Vec<_>>>()
            .map(|vec| U32::from(Box::try_from(vec).unwrap()))
    }

    pub fn simplify(&self) -> Self {
        U32::from_op(|i| self.bits[i].simplify())
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

impl Shl<usize> for &U32 {
    type Output = U32;

    fn shl(self, rhs: usize) -> Self::Output {
        assert!(rhs < 32);
        if rhs == 0 {
            return (*self).clone();
        }
        let mut bits = Vec::with_capacity(32);
        bits.extend(iter::repeat(Bool::from(false)).take(rhs));
        bits.extend_from_slice(&self.bits[..self.bits.len() - rhs]);
        U32::from(Box::try_from(bits).unwrap())
    }
}

impl Shr<usize> for &U32 {
    type Output = U32;

    fn shr(self, rhs: usize) -> Self::Output {
        assert!(rhs < 32);
        if rhs == 0 {
            return (*self).clone();
        }
        let mut bits = Vec::with_capacity(32);

        bits.extend_from_slice(&self.bits[rhs..]);
        bits.extend(iter::repeat(Bool::from(false)).take(rhs));
        U32::from(Box::try_from(bits).unwrap())
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

impl Mul for &U32 {
    type Output = U32;

    fn mul(self, rhs: Self) -> Self::Output {
        let zero = U32::from(0);
        let mut z = zero.clone();
        for (i, b) in rhs.bits.iter().enumerate() {
            z += &U32::ite(b, &(self << i), &zero);
        }
        z
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

macro_rules! binop_assign(($OpAssign:ident, $Rhs:ty, $op_assign:ident, $op:ident) => {
    impl $OpAssign<$Rhs> for U32 {
        fn $op_assign(&mut self, rhs: $Rhs) {
            *self = self.$op(rhs);
        }
    }
});

binop_assign!(BitAndAssign, &U32, bitand_assign, bitand);
binop_assign!(BitOrAssign, &U32, bitor_assign, bitor);
binop_assign!(BitXorAssign, &U32, bitxor_assign, bitxor);
binop_assign!(ShlAssign, usize, shl_assign, shl);
binop_assign!(ShrAssign, usize, shr_assign, shr);
binop_assign!(AddAssign, &U32, add_assign, add);
binop_assign!(SubAssign, &U32, sub_assign, sub);
binop_assign!(MulAssign, &U32, mul_assign, mul);

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
