use std::fmt::{self, Display, Formatter};

use crate::symbolic_bits::{Version, BV32};
use crate::{M, N};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct State {
    values: Box<[BV32; N]>,
    versions: Box<[Version; N]>,
}

impl State {
    pub fn new() -> Self {
        State {
            values: (0..N)
                .map(|i| BV32::new(i, Version::S0))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            versions: vec![Version::S0; N].try_into().unwrap(),
        }
    }

    fn get(&self, index: usize) -> BV32 {
        BV32::new(index, self.versions[index])
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

    pub fn twist(&mut self) {
        for i in 0..N - M {
            self.set(
                i,
                self.get(i + M)
                    ^ ((self.get(i) & 0x80000000) >> 1)
                    ^ ((self.get(i + 1) & 0x7ffffffe) >> 1)
                    ^ ((self.get(i + 1) & 0x1) * 0x9908b0df),
            );
        }
        for i in N - M..N - 1 {
            self.set(
                i,
                self.get(i - (N - M))
                    ^ ((self.get(i) & 0x80000000) >> 1)
                    ^ ((self.get(i + 1) & 0x7ffffffe) >> 1)
                    ^ ((self.get(i + 1) & 0x1) * 0x9908b0df),
            );
        }
        self.set(
            N - 1,
            self.get(M - 1)
                ^ ((self.get(N - 1) & 0x80000000) >> 1)
                ^ ((self.get(0) & 0x7ffffffe) >> 1)
                ^ ((self.get(0) & 0x1) * 0x9908b0df),
        );
    }
}

impl Display for State {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (i, v) in self.values.iter().enumerate() {
            writeln!(f, "[{i}]:\n{v}")?;
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
        println!("{state}");
    }
}
