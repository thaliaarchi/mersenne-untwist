use crate::{Random, N};

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
        const M: usize = 397;

        // Solving for bit 31 of state0[N - 1]:
        //
        // s1[623] == s1[396] ^ ((s0[623] & 0x80000000) >> 1) ^ ((s1[0] & 0x7ffffffe) >> 1) ^ ((s1[0] & 0x1) * 0x9908b0df)
        // s1[623] & 0x40000000 == (s1[396] ^ ((s0[623] & 0x80000000) >> 1) ^ ((s1[0] & 0x7ffffffe) >> 1) ^ ((s1[0] & 0x1) * 0x9908b0df)) & 0x40000000
        // s1[623] & 0x40000000 == (s1[396] ^ ((s0[623] & 0x80000000) >> 1)) & 0x40000000
        // s1[623] & 0x40000000 == (s1[396] ^ (s0[623] >> 1)) & 0x40000000
        // (s0[623] >> 1) & 0x40000000 == (s1[396] ^ s1[623]) & 0x40000000
        // s0[623] & 0x80000000 == ((s1[396] ^ s1[623]) << 1) & 0x80000000
        assert_eq!(
            state0[N - 1] & 0x80000000,
            ((state1[M - 1] ^ state1[N - 1]) << 1) & 0x80000000,
        );

        for i in N - M..N - 1 {
            // Solving for bit 0 of state0[i + 1]:
            //
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] & 0x80000000 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x80000000
            // s1[i] & 0x80000000 == (s1[i-(N-M)] ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x80000000
            // s1[i] & 0x80000000 == (s1[i-(N-M)] ^ (s0[i+1] << 31)) & 0x80000000
            // (s0[i+1] << 31) & 0x80000000 == (s1[i-(N-M)] ^ s1[i]) & 0x80000000
            // s0[i+1] & 0x1 == ((s1[i-(N-M)] ^ s1[i]) >> 31) & 0x1
            assert_eq!(
                state0[i + 1] & 0x1,
                ((state1[i - (N - M)] ^ state1[i]) >> 31) & 0x1,
            );

            // Solving for bit 31 of state0[i]:
            //
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] & 0x40000000 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x40000000
            // s1[i] & 0x40000000 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1)) & 0x40000000
            // s1[i] & 0x40000000 == (s1[i-(N-M)] ^ (s0[i] >> 1)) & 0x40000000
            // (s0[i] >> 1) & 0x40000000 == (s1[i-(N-M)] ^ s1[i]) & 0x40000000
            // s0[i] & 0x80000000 == ((s1[i-(N-M)] ^ s1[i]) << 1) & 0x80000000
            assert_eq!(
                state0[i] & 0x80000000,
                ((state1[i - (N - M)] ^ state1[i]) << 1) & 0x80000000,
            );

            // Solving for bits 6, 9–12, 15, 17–19, 21–24, 26–27, and 30 of
            // state0[i + 1]. The mask 0x26f74f20 is !0x9908b0df & !0x40000000,
            // that is, the zero bits of the magnitude constant, excluding bit
            // 30 which is handled above.
            //
            // s1[i] == s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)
            // s1[i] & 0x26f74f20 == (s1[i-(N-M)] ^ ((s0[i] & 0x80000000) >> 1) ^ ((s0[i+1] & 0x7ffffffe) >> 1) ^ ((s0[i+1] & 0x1) * 0x9908b0df)) & 0x26f74f20
            // s1[i] & 0x26f74f20 == (s1[i-(N-M)] ^ ((s0[i+1] & 0x7ffffffe) >> 1)) & 0x26f74f20
            // s1[i] & 0x26f74f20 == (s1[i-(N-M)] ^ (s0[i+1] >> 1)) & 0x26f74f20
            // (s0[i+1] >> 1) & 0x26f74f20 == (s1[i-(N-M)] ^ s1[i]) & 0x26f74f20
            // s0[i+1] & 0x4dee9e40 == ((s1[i-(N-M)] ^ s1[i]) << 1) & 0x4dee9e40
            assert_eq!(
                state0[i + 1] & 0x4dee9e40,
                ((state1[i - (N - M)] ^ state1[i]) << 1) & 0x4dee9e40,
            );
        }
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
