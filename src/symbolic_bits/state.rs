use std::fmt::{self, Display, Formatter};

use hashbrown::HashMap;

use crate::symbolic_bits::{Bit, Version, BV32};
use crate::{M, N};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    values: Box<[BV32; N]>,
    versions: Box<[Version; N]>,
}

#[derive(Clone, Debug)]
pub struct ValueClasses {
    classes: HashMap<BV32, Vec<u16>>,
}

impl State {
    pub fn new() -> Self {
        State {
            values: (0..N)
                .map(|i| BV32::new(i as isize, Version::S0))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            versions: vec![Version::S0; N].try_into().unwrap(),
        }
    }

    fn get(&self, index: usize, offset: isize) -> BV32 {
        let version = self.versions[index.checked_add_signed(offset).unwrap()];
        BV32::new(offset, version)
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

    pub fn value_classes(&mut self) -> ValueClasses {
        let mut classes: HashMap<BV32, Vec<u16>> = HashMap::new();
        for (i, v) in self.values.iter().enumerate() {
            classes.entry_ref(v).or_default().push(i as u16);
        }
        ValueClasses { classes }
    }

    pub fn twist(&mut self) {
        for i in 0..N - M {
            self.set(
                i,
                self.get(i, M as isize)
                    ^ ((self.get(i, 0) & 0x80000000) >> 1)
                    ^ ((self.get(i, 1) & 0x7ffffffe) >> 1)
                    ^ ((self.get(i, 1) & 0x1) * 0x9908b0df),
            );
        }
        for i in N - M..N - 1 {
            self.set(
                i,
                self.get(i, -((N - M) as isize))
                    ^ ((self.get(i, 0) & 0x80000000) >> 1)
                    ^ ((self.get(i, 1) & 0x7ffffffe) >> 1)
                    ^ ((self.get(i, 1) & 0x1) * 0x9908b0df),
            );
        }
        self.set(
            N - 1,
            self.get(N - 1, (M - 1) as isize - (N - 1) as isize)
                ^ ((self.get(N - 1, 0) & 0x80000000) >> 1)
                ^ ((self.get(N - 1, -((N - 1) as isize)) & 0x7ffffffe) >> 1)
                ^ ((self.get(N - 1, -((N - 1) as isize)) & 0x1) * 0x9908b0df),
        );
    }
}

impl Display for State {
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

impl Display for ValueClasses {
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
            writeln!(f, "{v}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn twist() {
        let mut state = State::new();
        state.twist();
        println!("{}", state.value_classes());
    }
}
