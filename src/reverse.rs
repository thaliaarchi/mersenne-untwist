use std::fmt::{self, Binary, Display, Formatter};

use crate::{Random, M, N};

impl Random {
    /// Reverses [`Random::from_u32`].
    pub fn unseed_u32(&self) -> Option<u32> {
        const MULT_INV: u32 = 2520285293; // MULT * MULT_INV == 1
        for i in (1..N).rev() {
            let si = self.state[i].wrapping_sub(i as u32).wrapping_mul(MULT_INV);
            if si != self.state[i - 1] ^ (self.state[i - 1] >> 30) {
                return None;
            }
        }
        Some(self.state[0])
    }

    /// Reverses [`Random::twist`].
    pub fn untwist_verify(state0: &[u32; N], state1: &[u32; N]) {
        use Version::*;

        let mut state = PartialState::new(state0, state1);

        for i in (N - M..N - 1).rev() {
            // (1) Solving for bit 0 of state0[i + 1]:
            //
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] & 0x80000000 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x80000000
            // s1[i] & 0x80000000 == (s1[i-(N-M)] ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x80000000
            // s1[i] & 0x80000000 == (s1[i-(N-M)] ^ (s0[i+1] << 31)) & 0x80000000
            // (s0[i+1] << 31) & 0x80000000 == (s1[i-(N-M)] ^ s1[i]) & 0x80000000
            // s0[i+1] & 0x1 == ((s1[i-(N-M)] ^ s1[i]) >> 31) & 0x1
            let lsb = (state.get(i - (N - M), 0x80000000, S1) ^ state.get(i, 0x80000000, S1)) >> 31;

            // (2) Solving for bit 31 of state0[i]:
            //
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] & 0x40000000 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x40000000
            // s1[i] & 0x40000000 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1)) & 0x40000000
            // s1[i] & 0x40000000 == (s1[i-(N-M)] ^ (s0[i] >> 1)) & 0x40000000
            // (s0[i] >> 1) & 0x40000000 == (s1[i-(N-M)] ^ s1[i]) & 0x40000000
            // s0[i] & 0x80000000 == ((s1[i-(N-M)] ^ s1[i]) << 1) & 0x80000000
            //
            // Solving for bit 31 of state0[N - 1]:
            //
            // s1[N-1] == s1[M-1] ^ ((s0[N-1] & 0x80000000) >> 1) ^ ((s1[0] & 0x7ffffffe) >> 1) ^ ((s1[0] & 0x1) * 0x9908b0df)
            // s1[N-1] & 0x40000000 == (s1[M-1] ^ ((s0[N-1] & 0x80000000) >> 1) ^ ((s1[0] & 0x7ffffffe) >> 1) ^ ((s1[0] & 0x1) * 0x9908b0df)) & 0x40000000
            // s1[N-1] & 0x40000000 == (s1[M-1] ^ ((s0[N-1] & 0x80000000) >> 1)) & 0x40000000
            // s1[N-1] & 0x40000000 == (s1[M-1] ^ (s0[N-1] >> 1)) & 0x40000000
            // (s0[N-1] >> 1) & 0x40000000 == (s1[M-1] ^ s1[N-1]) & 0x40000000
            // s0[N-1] & 0x80000000 == ((s1[M-1] ^ s1[N-1]) << 1) & 0x80000000
            //
            // The two are equivalent and the state0[N - 1] case extends the
            // range of the state0[i] case by 1, so i can be substituted with
            // `i + 1`.
            let msb = (state.get(i - (N - M) + 1, 0x40000000, S1)
                ^ state.get(i + 1, 0x40000000, S1))
                << 1;

            // (3) Solving for bits 1..=30 of state0[i + 1]:
            //
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ (lsb * 0x9908b0df)
            // s1[i] & 0x3fffffff == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ (lsb * 0x9908b0df)) & 0x3fffffff
            // s1[i] & 0x3fffffff == (s1[i-(N-M)] ^ (s0[i+1] >> 1) ^ (lsb * 0x9908b0df)) & 0x3fffffff
            // (s0[i+1] >> 1) & 0x3fffffff == (s1[i-(N-M)] ^ s1[i] ^ (lsb * 0x9908b0df)) & 0x3fffffff
            // s0[i+1] & 0x7ffffffe == ((s1[i-(N-M)] ^ s1[i] ^ (lsb * 0x9908b0df)) << 1) & 0x7ffffffe
            let mid = (state.get(i - (N - M), 0x3fffffff, S1)
                ^ state.get(i, 0x3fffffff, S1)
                ^ (lsb * 0x9908b0df))
                << 1;
            state.set(i + 1, msb | mid | lsb, 0xffffffff);
        }

        // This covers the state0[N - M] case of (2), that was skipped by
        // shifting up by 1.
        let msb = (state.get(N - M, 0x40000000, S1) ^ state.get(0, 0x40000000, S1)) << 1;
        state.set(N - M, msb, 0x80000000);

        for i in (0..N - M).rev() {
            // (4) Solving for bit 0 of state0[i + 1]. This is identical to (1),
            // except it uses s0[i+M], in place of s1[i-(N-M)].
            //
            // s1[i] == s0[i+M] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] & 0x80000000 == (s0[i+M] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x80000000
            // s1[i] & 0x80000000 == (s0[i+M] ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x80000000
            // s1[i] & 0x80000000 == (s0[i+M] ^ (s0[i+1] << 31)) & 0x80000000
            // (s0[i+1] << 31) & 0x80000000 == (s0[i+M] ^ s1[i]) & 0x80000000
            // s0[i+1] & 0x1 == ((s0[i+M] ^ s1[i]) >> 31) & 0x1
            let lsb = (state.get(i + M, 0x80000000, S0) ^ state.get(i, 0x80000000, S1)) >> 31;

            if i + M + 1 < N {
                let msb =
                    (state.get(i + M + 1, 0x40000000, S0) ^ state.get(i + 1, 0x40000000, S1)) << 1;
                state.set(i + 1, msb, 0x80000000);
            }

            // (5) Solving for bits 1..=30 of state0[i + 1]. This is identical
            // to (3), except it uses s0[i+M], in place of s1[i-(N-M)].
            //
            // s1[i] == s0[i+M] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] == s0[i+M] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ (lsb * 0x9908b0df)
            // s1[i] & 0x3fffffff == (s0[i+M] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ (lsb * 0x9908b0df)) & 0x3fffffff
            // s1[i] & 0x3fffffff == (s0[i+M] ^ (s0[i+1] >> 1) ^ (lsb * 0x9908b0df)) & 0x3fffffff
            // (s0[i+1] >> 1) & 0x3fffffff == (s0[i+M] ^ s1[i] ^ (lsb * 0x9908b0df)) & 0x3fffffff
            // s0[i+1] & 0x7ffffffe == ((s0[i+M] ^ s1[i] ^ (lsb * 0x9908b0df)) << 1) & 0x7ffffffe
            let mid = (state.get(i + M, 0x3fffffff, S0)
                ^ state.get(i, 0x3fffffff, S1)
                ^ (lsb * 0x9908b0df))
                << 1;
            state.set(i + 1, mid | lsb, 0x7fffffff);
        }

        println!("{state:b}");
    }

    /// Reverses [`Random::temper`].
    pub fn untemper(mut x: u32) -> u32 {
        // Reverse `x ^= x >> 18;`
        x ^= x >> 18;
        // Reverse `x ^= (x << 15) & 0xefc60000;`
        x ^= (x << 15) & 0x2fc60000;
        x ^= (x << 15) & 0xc0000000;
        // Reverse `x ^= (x << 7) & 0x9d2c5680;`
        x ^= (x << 7) & 0x00001680;
        x ^= (x << 7) & 0x000c4000;
        x ^= (x << 7) & 0x0d200000;
        x ^= (x << 7) & 0x90000000;
        // Reverse `x ^= x >> 11;`
        x ^= x >> 11;
        x ^= x >> 22;
        x
    }

    /// Equivalent to [`Random::untemper`], but operates on single bits.
    pub fn untemper_bits(x: u32) -> u32 {
        let x0 = (x >> 0) & 1;
        let x1 = (x >> 1) & 1;
        let x2 = (x >> 2) & 1;
        let x3 = (x >> 3) & 1;
        let x4 = (x >> 4) & 1;
        let x5 = (x >> 5) & 1;
        let x6 = (x >> 6) & 1;
        let x7 = (x >> 7) & 1;
        let x8 = (x >> 8) & 1;
        let x9 = (x >> 9) & 1;
        let x10 = (x >> 10) & 1;
        let x11 = (x >> 11) & 1;
        let x12 = (x >> 12) & 1;
        let x13 = (x >> 13) & 1;
        let x14 = (x >> 14) & 1;
        let x15 = (x >> 15) & 1;
        let x16 = (x >> 16) & 1;
        let x17 = (x >> 17) & 1;
        let x18 = (x >> 18) & 1;
        let x19 = (x >> 19) & 1;
        let x20 = (x >> 20) & 1;
        let x21 = (x >> 21) & 1;
        let x22 = (x >> 22) & 1;
        let x23 = (x >> 23) & 1;
        let x24 = (x >> 24) & 1;
        let x25 = (x >> 25) & 1;
        let x26 = (x >> 26) & 1;
        let x27 = (x >> 27) & 1;
        let x28 = (x >> 28) & 1;
        let x29 = (x >> 29) & 1;
        let x30 = (x >> 30) & 1;
        let x31 = (x >> 31) & 1;

        (x0 ^ x7 ^ x11 ^ x18 ^ x22 ^ x25 ^ x29) << 0
            | (x1 ^ x5 ^ x8 ^ x12 ^ x19 ^ x23 ^ x23 ^ x26 ^ x30) << 1
            | (x9 ^ x13 ^ x17 ^ x24 ^ x27 ^ x31) << 2
            | (x3 ^ x0 ^ x7 ^ x10 ^ x14 ^ x18 ^ x21 ^ x28) << 3
            | (x4 ^ x5 ^ x11 ^ x12 ^ x15 ^ x19 ^ x22 ^ x23 ^ x26 ^ x29 ^ x30) << 4
            | (x5 ^ x12 ^ x16 ^ x20 ^ x23 ^ x27 ^ x30) << 5
            | (x6 ^ x0 ^ x2 ^ x7 ^ x14 ^ x17 ^ x18 ^ x20 ^ x21 ^ x24 ^ x25 ^ x28) << 6
            | (x7 ^ x0 ^ x3 ^ x11 ^ x14 ^ x18 ^ x18 ^ x21 ^ x25 ^ x29 ^ x29) << 7
            | (x8 ^ x5 ^ x12 ^ x15 ^ x19 ^ x23 ^ x26) << 8
            | (x16 ^ x17 ^ x20 ^ x24 ^ x31) << 9
            | (x10 ^ x0 ^ x3 ^ x7 ^ x14 ^ x18 ^ x21 ^ x21 ^ x25 ^ x28) << 10
            | (x11 ^ x7 ^ x22 ^ x25 ^ x29) << 11
            | (x12 ^ x5 ^ x8 ^ x23 ^ x23 ^ x26 ^ x30) << 12
            | (x13 ^ x2 ^ x9 ^ x17 ^ x20 ^ x24 ^ x27 ^ x31) << 13
            | (x14 ^ x0 ^ x7 ^ x10 ^ x18 ^ x28) << 14
            | (x15 ^ x5 ^ x11 ^ x12 ^ x19 ^ x23 ^ x26 ^ x29 ^ x30) << 15
            | (x16 ^ x12 ^ x20 ^ x27 ^ x30) << 16
            | (x17 ^ x0 ^ x2 ^ x7 ^ x14 ^ x18 ^ x20 ^ x21 ^ x25 ^ x28) << 17
            | (x18 ^ x3 ^ x11 ^ x14 ^ x21 ^ x29 ^ x29) << 18
            | (x19 ^ x5 ^ x12 ^ x15 ^ x23) << 19
            | (x2 ^ x9 ^ x16 ^ x17 ^ x24 ^ x27 ^ x31) << 20
            | (x21 ^ x0 ^ x7 ^ x14 ^ x18 ^ x25) << 21
            | (x22 ^ x7 ^ x25) << 22
            | (x23 ^ x8 ^ x26) << 23
            | (x24 ^ x2 ^ x9 ^ x17 ^ x20 ^ x27) << 24
            | (x25 ^ x10 ^ x28) << 25
            | (x26 ^ x5 ^ x11 ^ x12 ^ x19 ^ x23 ^ x29 ^ x30) << 26
            | (x27 ^ x12 ^ x20 ^ x30) << 27
            | (x28 ^ x0 ^ x7 ^ x14 ^ x18 ^ x21 ^ x25) << 28
            | (x29 ^ x14) << 29
            | (x30 ^ x15) << 30
            | (x31 ^ x2 ^ x9 ^ x16 ^ x17 ^ x20 ^ x24 ^ x27) << 31
    }
}

#[derive(Clone, Debug)]
struct PartialState<'a> {
    values: [u32; N],
    reversed: [u32; N],
    state0_verify: &'a [u32; N],
    state1_verify: &'a [u32; N],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Version {
    S0,
    S1,
}

impl<'a> PartialState<'a> {
    fn new(state0: &'a [u32; N], state1: &'a [u32; N]) -> Self {
        PartialState {
            values: *state1,
            reversed: [0; N],
            state0_verify: state0,
            state1_verify: state1,
        }
    }

    fn get(&mut self, i: usize, mask: u32, version: Version) -> u32 {
        // The mask and version are just to assert well-formedness and are not
        // used in the result.
        assert!(
            match version {
                Version::S0 => self.reversed[i] & mask == mask,
                Version::S1 => !self.reversed[i] & mask == mask,
            },
            "get {version}[{i}]\n\
                reversed = {reversed:08x} {reversed:032b}\n\
                mask     = {mask:08x} {mask:032b}",
            reversed = self.reversed[i],
        );
        self.values[i] & mask
    }

    fn set(&mut self, i: usize, value: u32, mask: u32) {
        assert!(self.reversed[i] & mask == 0, "set state0[{i}]");
        assert!(
            value & mask == self.state0_verify[i] & mask,
            "set state0[{i}]\n\
                value    = {value:08x} {value:032b}\n\
                expected = {expected:08x} {expected:032b}\n\
                reversed = {reversed:08x} {reversed:032b}\n\
                mask     = {mask:08x} {mask:032b}",
            expected = self.state0_verify[i],
            reversed = self.reversed[i],
        );
        self.values[i] &= !mask;
        self.values[i] |= value & mask;
        self.reversed[i] |= mask;
    }

    fn bits_reversed(&self) -> u32 {
        self.reversed.iter().map(|&mask| mask.count_ones()).sum()
    }

    fn write_stat(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let reversed = self.bits_reversed();
        let total = N * 32;
        let percent = (reversed as f64 / total as f64) * 100.0;
        writeln!(f, "{reversed} / {total} bits reversed ({percent:.1}%)")
    }
}

impl Display for PartialState<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for i in 0..N {
            writeln!(
                f,
                "[{i:3}]: \
                    s0 part = {:08x} in {:08x}, \
                    s1 part = {:08x} in {:08x}, \
                    s0 = {:08x}, \
                    s1 = {:08x}",
                self.values[i] & self.reversed[i],
                self.reversed[i],
                self.values[i] & !self.reversed[i],
                !self.reversed[i],
                self.state0_verify[i],
                self.state1_verify[i],
            )?;
        }
        self.write_stat(f)
    }
}

impl Binary for PartialState<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fn write_part(f: &mut Formatter<'_>, value: u32, mask: u32) -> fmt::Result {
            for i in (0..32).rev() {
                if mask & (1 << i) != 0 {
                    write!(f, "{}", (value >> i) & 1)?;
                } else {
                    write!(f, ".")?;
                }
            }
            Ok(())
        }

        for i in 0..N {
            write!(f, "[{i:3}]: s0 part = ")?;
            write_part(f, self.values[i], self.reversed[i])?;
            write!(f, ", s1 part = ")?;
            write_part(f, self.values[i], !self.reversed[i])?;
            writeln!(
                f,
                ", s0 = {:032b}, s1 = {:032b}",
                self.state0_verify[i], self.state1_verify[i],
            )?;
        }
        self.write_stat(f)
    }
}

impl Display for Version {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Version::S0 => write!(f, "state0"),
            Version::S1 => write!(f, "state1"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unseed_u32_round() {
        assert_eq!(Random::from_u32(123).unseed_u32(), Some(123));
    }

    #[test]
    fn untemper_round() {
        assert_eq!(Random::untemper(Random::temper(0x1234abcd)), 0x1234abcd);
        assert_eq!(
            Random::untemper_bits(Random::temper(0x1234abcd)),
            0x1234abcd,
        );
    }
}
