use std::fmt::{self, Display, Formatter};
use std::ops::{BitXor, Index};

use crate::N;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    values: Box<[(Value, Version); N]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Symbol {
    index: u16,
    version: Version,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Version {
    Pre,
    Post,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    /// `x`
    Symbol(Symbol),
    /// `x ^ y`
    Xor(Box<Value>, Box<Value>),
    /// `x & 0x7ffffffe`
    Mid(Box<Value>),
    /// `x & 0x80000000`
    Msb(Box<Value>),
    /// `(x & 0x1) * 0x9908b0df`
    Mag(Box<Value>),
}

impl State {
    pub fn new() -> Self {
        State {
            values: (0..N)
                .map(|i| (Value::Symbol(Symbol::new(i, Version::Pre)), Version::Pre))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn symbol(&self, index: usize) -> Value {
        Value::Symbol(Symbol {
            index: index as u16,
            version: self.values[index].1,
        })
    }
}

impl Index<usize> for State {
    type Output = Value;

    fn index(&self, index: usize) -> &Self::Output {
        &self.values[index].0
    }
}

impl Symbol {
    pub fn new(index: usize, version: Version) -> Self {
        Symbol {
            index: index as u16,
            version,
        }
    }
}

impl BitXor for Value {
    type Output = Value;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Value::Xor(Box::new(self), Box::new(rhs))
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.version {
            Version::Pre => write!(f, "s{}", self.index),
            Version::Post => write!(f, "s{}'", self.index),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Value::Symbol(sym) => write!(f, "{sym}"),
            Value::Xor(x, y) => write!(f, "{x} ^ {y}"),
            Value::Mid(x) => write!(f, "mid({x})"),
            Value::Msb(x) => write!(f, "msb({x})"),
            Value::Mag(x) => write!(f, "mag({x})"),
        }
    }
}

impl Display for State {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (i, &(ref v, version)) in self.values.iter().enumerate() {
            writeln!(f, "{} = {v}", Symbol::new(i, version))?;
        }
        Ok(())
    }
}
