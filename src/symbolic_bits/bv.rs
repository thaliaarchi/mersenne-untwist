use std::fmt::{self, Display, Formatter};
use std::ops::{
    BitAnd, BitAndAssign, BitXor, BitXorAssign, Mul, MulAssign, Shl, ShlAssign, Shr, ShrAssign,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BV32 {
    bits: Box<[Bit; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bit {
    Const(bool),
    Ref(Var),
    Xor(Box<Bit>, Box<Bit>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Var {
    index: u16,
    bit: u8,
    version: Version,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Version {
    S0 = 0,
    S1 = 1,
}

impl BV32 {
    pub fn new(index: usize, version: Version) -> Self {
        BV32 {
            bits: (0..32)
                .map(|bit| Bit::Ref(Var::new(index, bit, version)))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }
}

impl Var {
    pub fn new(index: usize, bit: usize, version: Version) -> Self {
        Var {
            index: index as u16,
            bit: bit as u8,
            version,
        }
    }
}

impl BitXorAssign for BV32 {
    fn bitxor_assign(&mut self, rhs: BV32) {
        for i in 0..32 {
            // TODO: clones
            self.bits[i] = self.bits[i].clone() ^ rhs.bits[i].clone();
        }
    }
}

impl BitAndAssign<u32> for BV32 {
    fn bitand_assign(&mut self, rhs: u32) {
        for i in 0..32 {
            if rhs & (1 << i) == 0 {
                self.bits[i] = Bit::Const(false);
            }
        }
    }
}

impl ShlAssign<usize> for BV32 {
    fn shl_assign(&mut self, rhs: usize) {
        assert!(rhs < 32);
        for i in 0..rhs {
            self.bits[i] = self.bits[rhs + i].clone(); // TODO: clone
        }
    }
}

impl ShrAssign<usize> for BV32 {
    fn shr_assign(&mut self, rhs: usize) {
        assert!(rhs < 32);
        for i in 0..rhs {
            self.bits[rhs + i] = self.bits[i].clone(); // TODO: clone
        }
    }
}

impl MulAssign<u32> for BV32 {
    fn mul_assign(&mut self, rhs: u32) {
        for i in 1..32 {
            assert_eq!(
                self.bits[i],
                Bit::Const(false),
                "only (x & 0x1) & y is implemented",
            );
        }
        if self.bits[0] != Bit::Const(false) {
            for i in 1..32 {
                if rhs & (1 << i) != 0 {
                    self.bits[i] = self.bits[0].clone();
                }
            }
        }
    }
}

impl BitXor for BV32 {
    type Output = BV32;

    fn bitxor(mut self, rhs: BV32) -> Self::Output {
        self ^= rhs;
        self
    }
}

impl BitAnd<u32> for BV32 {
    type Output = BV32;

    fn bitand(mut self, rhs: u32) -> Self::Output {
        self &= rhs;
        self
    }
}

impl Shl<usize> for BV32 {
    type Output = BV32;

    fn shl(mut self, rhs: usize) -> Self::Output {
        self <<= rhs;
        self
    }
}

impl Shr<usize> for BV32 {
    type Output = BV32;

    fn shr(mut self, rhs: usize) -> Self::Output {
        self >>= rhs;
        self
    }
}

impl Mul<u32> for BV32 {
    type Output = BV32;

    fn mul(mut self, rhs: u32) -> Self::Output {
        self *= rhs;
        self
    }
}

impl BitXor for Bit {
    type Output = Bit;

    fn bitxor(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (Bit::Const(x), Bit::Const(y)) => Bit::Const(x != y),
            (_, Bit::Const(false)) => self,
            (Bit::Const(false), _) => rhs,
            _ => Bit::Xor(Box::new(self), Box::new(rhs)),
        }
    }
}

impl BitAnd<bool> for Bit {
    type Output = Bit;

    fn bitand(self, rhs: bool) -> Self::Output {
        if rhs {
            self
        } else {
            Bit::Const(false)
        }
    }
}

impl BitAnd<bool> for &Bit {
    type Output = Bit;

    fn bitand(self, rhs: bool) -> Self::Output {
        if rhs {
            self.clone()
        } else {
            Bit::Const(false)
        }
    }
}

impl Display for BV32 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (i, bit) in self.bits.iter().enumerate() {
            writeln!(f, ".{i} = {bit}")?;
        }
        Ok(())
    }
}

impl Display for Bit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Bit::Const(false) => write!(f, "0"),
            Bit::Const(true) => write!(f, "1"),
            Bit::Ref(v) => write!(f, "{v}"),
            Bit::Xor(x, y) => write!(f, "{x} ^ {y}"),
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "s{}.{}.{}", self.version as u8, self.index, self.bit)
    }
}

impl Display for Version {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "state{}", *self as u8)
    }
}
