use std::fmt::{self, Display, Formatter};
use std::ops::{BitXor, Index};

use crate::N;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    values: Box<[(Value, Version); N]>,
    transparent_symbols: bool,
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
    Unary(Unary, Box<Value>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unary {
    /// `x & 0x7ffffffe`
    Mid,
    /// `x & 0x80000000`
    Msb,
    /// `(x & 0x1) * 0x9908b0df`
    Mag,
    /// `x >> 1`
    Shr1,
}

impl State {
    pub fn new() -> Self {
        State {
            values: (0..N)
                .map(|i| (Value::Symbol(Symbol::new(i, Version::Pre)), Version::Pre))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            transparent_symbols: false,
        }
    }

    pub fn transparent_symbols(&mut self, transparent_symbols: bool) {
        self.transparent_symbols = transparent_symbols;
    }

    pub fn get(&self, index: usize) -> Value {
        if self.transparent_symbols {
            self.values[index].0.clone()
        } else {
            Value::Symbol(Symbol {
                index: index as u16,
                version: self.values[index].1,
            })
        }
    }

    pub fn set(&mut self, index: usize, v: Value) {
        assert_eq!(self.values[index].1, Version::Pre);
        self.values[index] = (v, Version::Post);
    }

    pub fn eval(&self, state: &[u32; N]) -> [u32; N] {
        let mut state1 = state.clone();
        for (i, (v, _)) in self.values.iter().enumerate() {
            state1[i] = v.eval(self, state, &state1);
        }
        state1
    }

    pub fn twist(&mut self) {
        const M: usize = 397;
        for k in 0..N - M {
            let v = self.get(k + M)
                ^ Value::shr1(Value::msb(self.get(k)))
                ^ Value::shr1(Value::mid(self.get(k + 1)))
                ^ Value::mag(self.get(k + 1));
            self.set(k, v);
        }
        for k in N - M..N - 1 {
            let v = self.get(k - (N - M))
                ^ Value::shr1(Value::msb(self.get(k)))
                ^ Value::shr1(Value::mid(self.get(k + 1)))
                ^ Value::mag(self.get(k + 1));
            self.set(k, v);
        }
        let v = self.get(M - 1)
            ^ Value::shr1(Value::msb(self.get(N - 1)))
            ^ Value::shr1(Value::mid(self.get(0)))
            ^ Value::mag(self.get(0));
        self.set(N - 1, v);
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

impl Value {
    pub fn mid(x: Value) -> Self {
        Value::Unary(Unary::Mid, Box::new(x))
    }
    pub fn msb(x: Value) -> Self {
        Value::Unary(Unary::Msb, Box::new(x))
    }
    pub fn mag(x: Value) -> Self {
        Value::Unary(Unary::Mag, Box::new(x))
    }
    pub fn shr1(x: Value) -> Self {
        Value::Unary(Unary::Shr1, Box::new(x))
    }

    pub fn eval(&self, state: &State, state0: &[u32], state1: &[u32]) -> u32 {
        match self {
            Value::Symbol(sym) => match sym.version {
                Version::Pre => state0[sym.index as usize],
                Version::Post => state1[sym.index as usize],
            },
            Value::Xor(x, y) => {
                let x = x.eval(state, state0, state1);
                let y = y.eval(state, state0, state1);
                x ^ y
            }
            Value::Unary(op, x) => {
                let x = x.eval(state, state0, state1);
                match op {
                    Unary::Mid => x & 0x7ffffffe,
                    Unary::Msb => x & 0x80000000,
                    Unary::Mag => (x & 0x1) * 0x9908b0df,
                    Unary::Shr1 => x >> 1,
                }
            }
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
            Version::Post => write!(f, "s'{}", self.index),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Value::Symbol(sym) => write!(f, "{sym}"),
            Value::Xor(x, y) => write!(f, "{x} ^ {y}"),
            Value::Unary(op, x) => match **x {
                Value::Symbol(_) => write!(f, "{op} {x}"),
                Value::Xor(_, _) | Value::Unary(_, _) => write!(f, "{op}({x})"),
            },
        }
    }
}

impl Display for Unary {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Unary::Mid => write!(f, "mid"),
            Unary::Msb => write!(f, "msb"),
            Unary::Mag => write!(f, "mag"),
            Unary::Shr1 => write!(f, "shr1"),
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

#[cfg(test)]
mod tests {
    use crate::Random;

    use super::*;

    #[test]
    fn twist() {
        let mut rand = Random::from_u32(12345);
        let state0 = rand.state().clone();
        rand.twist();
        let state1 = rand.state().clone();

        let mut s = State::new();
        s.transparent_symbols(true);
        s.twist();

        println!("{s}");
        assert_eq!(s.eval(&state0), state1);
    }
}
