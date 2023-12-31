use crate::{global_z3::U32, Random, M, N};

#[derive(Debug, Clone)]
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
            state.push(v.simplify())
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
            state[i] = ((&state[i] ^ ((prev ^ (prev >> shift)) * mult1)) + key0).simplify();
        }
        let last = &state[N - 1];
        state[1] = ((&state[1] ^ ((last ^ (last >> shift)) * mult1)) + key0).simplify();

        for i in 2..N {
            let prev = &state[i - 1];
            state[i] =
                ((&state[i] ^ ((prev ^ (prev >> shift)) * mult2)) - U32::from(i as u32)).simplify();
        }
        let last = &state[N - 1];
        state[1] = ((&state[1] ^ ((last ^ (last >> shift)) * mult2)) - &U32::from(1)).simplify();

        state[0] = U32::from(0x80000000);
        Z3Random::from_state(state)
    }

    pub fn from_state(state: Box<[U32; N]>) -> Self {
        Z3Random { state, index: N }
    }

    pub fn state(&self) -> &[U32; N] {
        &self.state
    }

    fn twist(&mut self) {
        let matrix_a = &U32::from(0x9908b0df);
        let msb_mask = &U32::from(0x80000000);
        let mid_mask = &U32::from(0x7ffffffe);
        let zero = &U32::from(0);
        let one = &U32::from(1);

        let state = &mut self.state;
        for k in 0..N {
            let y = (&state[k] & msb_mask) | (&state[(k + 1) % N] & mid_mask);
            let mag = U32::ite(&(&state[(k + 1) % N] & one).equals(zero), zero, matrix_a);
            state[k] = (&state[(k + M) % N] ^ (y >> one) ^ mag).simplify();
        }
    }

    pub fn temper(mut x: U32) -> U32 {
        x ^= &x >> 11;
        x ^= (&x << 7) & 0x9d2c5680;
        x ^= (&x << 15) & 0xefc60000;
        x ^= &x >> 18;
        x
    }

    pub fn untemper(mut x: U32) -> U32 {
        // Reverse `x ^= &x >> 18;`
        x ^= &x >> 18;
        // Reverse `x ^= (&x << 15) & 0xefc60000;`
        x ^= (&x << 15) & 0x2fc60000;
        x ^= (&x << 15) & 0xc0000000;
        // Reverse `x ^= (&x << 7) & 0x9d2c5680;`
        x ^= (&x << 7) & 0x00001680;
        x ^= (&x << 7) & 0x000c4000;
        x ^= (&x << 7) & 0x0d200000;
        x ^= (&x << 7) & 0x90000000;
        // Reverse `x ^= &x >> 11;`
        x ^= &x >> 11;
        x ^= &x >> 22;
        x
    }

    pub fn next_u32(&mut self) -> U32 {
        if self.index == N {
            self.twist();
            self.index = 0;
        }
        let y = self.state[self.index].clone();
        self.index += 1;
        Z3Random::temper(y)
    }

    pub fn simplify(&mut self) {
        for x in self.state.iter_mut() {
            *x = x.simplify();
        }
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

        let mut z3rand = Z3Random::from_u32_const(seed);
        let x_var = z3rand.next_u32();
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
        let seed = 123;
        let mut rand = Random::from_u32(seed);

        let seed_var = U32::new(CStr::from_bytes_with_nul(b"seed\0").unwrap());
        let mut z3rand = Z3Random::from_u32(&seed_var);
        let solver = Solver::new();
        for _ in 0..N {
            let v = z3rand.next_u32();
            solver.assert(&v.equals(&U32::from(rand.next_u32())));
        }
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let seed_const = seed_var.eval(&model, true).unwrap().as_const().unwrap();
        assert_eq!(seed_const, 123);
    }

    #[test]
    fn twist() {
        let state = (0..N)
            .map(|i| {
                let s = format!("s{i}\0");
                U32::new(CStr::from_bytes_with_nul(s.as_bytes()).unwrap())
            })
            .collect::<Vec<_>>();
        let mut z3rand = Z3Random::from_state(state.try_into().unwrap());
        z3rand.twist();
        for (i, x) in z3rand.state().iter().enumerate() {
            println!("state[{i}] = {x}");
        }
    }
}
