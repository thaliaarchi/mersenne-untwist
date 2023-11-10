use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

use crate::symbolic_bits::{Bit, Version, BV32};
use crate::{M, N};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State<const N: usize = { crate::N }> {
    values: Box<[BV32; N]>,
    versions: Box<[Version; N]>,
}

#[derive(Clone, Debug)]
pub struct ValueClasses<'a> {
    classes: HashMap<&'a BV32, Vec<u16>>,
}

impl<const N: usize> State<N> {
    pub fn new() -> Self {
        State {
            values: (0..N)
                .map(|i| BV32::new(i, i, Version::S0))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            versions: vec![Version::S0; N].try_into().unwrap(),
        }
    }

    fn get(&self, user: usize, index: usize) -> BV32 {
        BV32::new(user, index, self.versions[index])
    }

    fn set(&mut self, index: usize, value: BV32) {
        assert_eq!(
            self.versions[index],
            Version::S0,
            "state[{index}] already assigned",
        );
        self.values[index] = value;
        self.versions[index] = Version::S1;
    }

    pub fn value_classes<'a>(&'a mut self) -> ValueClasses<'a> {
        let mut classes: HashMap<&'a BV32, Vec<u16>> = HashMap::new();
        for (i, v) in self.values.iter().enumerate() {
            classes.entry(v).or_default().push(i as u16);
        }
        ValueClasses { classes }
    }

    pub fn eval(&self, state0: &[u32; N], state1: &[u32; N]) -> [u32; N] {
        let mut state = [0; N];
        for (i, abs_v) in self.values.iter().enumerate() {
            let mut v = 0;
            for (j, abs_bit) in abs_v.bits.iter().enumerate() {
                let bit = match abs_bit {
                    Bit::Const(b) => *b as u32,
                    Bit::Xor(xs) => {
                        let mut b = 0;
                        for x in xs {
                            let s = match x.version() {
                                Version::S0 => state0,
                                Version::S1 => state1,
                            };
                            b ^= (s[x.index()] >> x.bit()) & 1;
                        }
                        b
                    }
                };
                v |= bit << j;
            }
            state[i] = v;
        }
        state
    }
}

impl State<N> {
    pub fn twist(&mut self) {
        for i in 0..N {
            let x = self.get(i, (i + M) % N)
                ^ ((self.get(i, i % N) & 0x80000000) >> 1)
                ^ ((self.get(i, (i + 1) % N) & 0x7ffffffe) >> 1)
                ^ ((self.get(i, (i + 1) % N) & 0x1) * 0x9908b0df);
            self.set(i, x);
        }
    }
}

impl<const N: usize> Display for State<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            writeln!(f, "digraph mt19937_state {{")?;
            for (i, v) in self.values.iter().enumerate() {
                for (j, bit) in v.bits.iter().enumerate() {
                    match bit {
                        Bit::Const(true) => {
                            writeln!(f, "    \"s1.{i}.{j}\" -> const0;")?;
                        }
                        Bit::Const(false) => {
                            writeln!(f, "    \"s1.{i}.{j}\" -> const1;")?;
                        }
                        Bit::Xor(xs) => {
                            for var in xs {
                                writeln!(f, "    \"s1.{i}.{j}\" -> \"{var}\";")?;
                            }
                        }
                    }
                }
                writeln!(f)?;
            }
            writeln!(f, "}}")?;
        } else {
            for (i, v) in self.values.iter().enumerate() {
                writeln!(f, "[{i}]:\n{v}")?;
            }
        }
        Ok(())
    }
}

impl Display for ValueClasses<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut classes = self.classes.iter().collect::<Vec<_>>();
        classes.sort_by(|(_, i1), (_, i2)| i1[0].cmp(&i2[0]));
        for (v, indices) in classes {
            write!(f, "class ")?;
            let mut i = 0;
            while i < indices.len() {
                let start = indices[i];
                let mut end = start;
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{start}")?;
                i += 1;
                while i < indices.len() && indices[i] == end + 1 {
                    end = indices[i];
                    i += 1;
                }
                if start != end {
                    write!(f, "–{end}")?;
                }
            }
            writeln!(f, " =")?;
            writeln!(f, "{v:+}")?;
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
        s.twist();
        println!("{}", s.value_classes());
        let state1_sym = s.eval(&state0, &state1);
        if state1_sym != state1 {
            for i in 0..N {
                if state1_sym[i] != state1[i] {
                    println!(
                        "[{i:3}]:\n\
                        symbolic s1 = {:032b}\n\
                        concrete s1 = {:032b}\n\
                        s0          = {:032b}",
                        state1_sym[i], state1[i], state0[i],
                    );
                }
            }
            panic!("symbolic evaluation differs from concrete");
        }
    }

    #[test]
    fn eval() {
        let state0 = [0x123, 0x456, 0x789];
        let [mut x, mut y, mut z] = state0;
        x = (((x << 12) ^ y) << 12) ^ z;
        z = x ^ y;
        y = ((z >> 3) & 1) * 0x9876543;
        let state1 = [x, y, z];

        let x = {
            let x = BV32::new(0, 0, Version::S0);
            let y = BV32::new(0, 1, Version::S0);
            let z = BV32::new(0, 2, Version::S0);
            (((x << 12) ^ y) << 12) ^ z
        };
        let z = {
            let x = BV32::new(2, 0, Version::S1);
            let y = BV32::new(2, 1, Version::S0);
            x ^ y
        };
        let y = {
            let z = BV32::new(1, 2, Version::S1);
            ((z >> 3) & 1) * 0x9876543
        };
        let state = State::<3> {
            values: Box::new([x, y, z]),
            versions: Box::new([Version::S1; 3]),
        };

        let state1_sym = state.eval(&state0, &state1);
        if state1_sym != state1 {
            println!("symbolic state1 = {state1_sym:08x?}");
            println!("state1          = {state1:08x?}");
            panic!("symbolic evaluation differs from concrete");
        }
    }
}
