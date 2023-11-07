use crate::{global_z3::U32, Random, N};

pub struct Z3Random {
    state: Box<[U32; N]>,
    index: usize,
}

impl Z3Random {
    pub fn from_u32(seed: &U32) -> Z3Random {
        let mult = &U32::from(1812433253);
        let shift = &U32::from(30);
        let mut state = Vec::with_capacity(N);
        state.push(seed.clone());
        for i in 1..N {
            let prev = &state[i - 1];
            let v = (prev ^ (prev >> shift)) * mult + U32::from(i as u32);
            state.push(v)
        }
        let state = state.try_into().unwrap();
        Z3Random::from_state(state)
    }

    pub fn from_u32_const(seed: u32) -> Z3Random {
        let state = Random::from_u32(seed)
            .state()
            .map(|n| U32::from(n))
            .try_into()
            .unwrap();
        Z3Random::from_state(state)
    }

    pub fn from_array1(key0: &U32) -> Z3Random {
        let mult1 = &U32::from(1664525);
        let mult2 = &U32::from(1566083941);
        let shift = &U32::from(30);

        let mut state = Z3Random::from_u32_const(19650218).state;

        for i in 1..N {
            let prev = &state[i - 1];
            state[i] = (&state[i] ^ ((prev ^ (prev >> shift)) * mult1)) + key0;
        }
        let last = &state[N - 1];
        state[1] = (&state[1] ^ ((last ^ (last >> shift)) * mult1)) + key0;

        for i in 2..N {
            let prev = &state[i - 1];
            state[i] = (&state[i] ^ ((prev ^ (prev >> shift)) * mult2)) - U32::from(i as u32);
        }
        let last = &state[N - 1];
        state[1] = (&state[1] ^ ((last ^ (last >> shift)) * mult2)) - &U32::from(1);

        state[0] = U32::from(0x80000000);
        Z3Random::from_state(state)
    }

    pub fn from_state(state: Box<[U32; N]>) -> Self {
        Z3Random { state, index: N }
    }

    pub fn next_u32(&mut self) -> U32 {
        const M: usize = 397;
        let matrix_a = &U32::from(0x9908b0df);
        let upper_mask = &U32::from(0x80000000);
        let lower_mask = &U32::from(0x7fffffff);
        let zero = &U32::from(0);
        let one = &U32::from(1);

        let state = &mut self.state;

        if self.index == N {
            for k in 0..N - M {
                let y = (&state[k] & upper_mask) | (&state[k + 1] & lower_mask);
                let mag = (&y & one).equals(zero).ite(zero, matrix_a);
                state[k] = &state[k + M] ^ (y >> one) ^ mag;
            }
            for k in N - M..N - 1 {
                let y = (&state[k] & upper_mask) | (&state[k + 1] & lower_mask);
                let mag = (&y & one).equals(zero).ite(zero, matrix_a);
                state[k] = &state[k - (N - M)] ^ (y >> one) ^ mag;
            }
            let y = (&state[N - 1] & upper_mask) | (&state[0] & lower_mask);
            let mag = (&y & one).equals(zero).ite(zero, matrix_a);
            state[N - 1] = &state[M - 1] ^ (y >> one) ^ mag;

            self.index = 0;
        }

        let mut y = state[self.index].clone();
        self.index += 1;

        y ^= &y >> U32::from(11);
        y ^= (&y << U32::from(7)) & U32::from(0x9d2c5680);
        y ^= (&y << U32::from(15)) & U32::from(0xefc60000);
        y ^= &y >> U32::from(18);
        y
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::CStr;

    use crate::global_z3::{SatResult, Solver};

    use super::*;

    #[test]
    fn abstract_matches_concrete() {
        let seed = 123;

        let mut arand = Z3Random::from_u32_const(seed);
        let x_var = arand.next_u32();
        let solver = Solver::new();
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let x = x_var.eval(&model, true).unwrap().as_const().unwrap();

        let mut rand = Random::from_u32(seed);
        assert_eq!(x, rand.next_u32());
    }

    #[test]
    #[ignore = "too slow"]
    fn solve_seed() {
        let seed_var = U32::new(CStr::from_bytes_until_nul(b"seed\0").unwrap());
        let mut arand = Z3Random::from_u32(&seed_var);
        let x = arand.next_u32();
        let solver = Solver::new();
        solver.assert(&x.equals(&U32::from(0xb24bcdfe)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let seed = seed_var.eval(&model, true).unwrap().as_const().unwrap();
        assert_eq!(seed, 123);
    }
}
