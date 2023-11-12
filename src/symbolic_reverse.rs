use std::ffi::CStr;

use crate::{
    global_z3::{Solver, U32},
    M, N,
};

#[derive(Clone, Debug)]
pub struct Random {
    forward: State,
    index: usize,
    seed: [U32; 1],
    solver: Solver,
}

#[derive(Clone, Debug)]
pub struct State {
    values: Box<[U32; N]>,
}

impl Random {
    pub fn new() -> Self {
        let state = State::new();
        let mut reverse = state.clone();
        reverse.untwist();
        let mut solver = Solver::new();
        let seed = reverse.recover_seed_array1(&mut solver);
        Random {
            forward: state,
            index: 0,
            seed,
            solver,
        }
    }

    pub fn next_u32(&mut self) -> &U32 {
        if self.index >= N {
            self.forward.twist();
            self.index = 0;
        }
        let value = &self.forward.values[self.index];
        self.index += 1;
        value
    }

    pub fn seed(&self) -> [&U32; 1] {
        [&self.seed[0]]
    }

    pub fn solver(&mut self) -> &mut Solver {
        &mut self.solver
    }
}

impl State {
    pub fn new() -> Self {
        let values: Box<[U32; N]> = (0..N)
            .map(|i| {
                let s = format!("s{i}\0");
                U32::new(CStr::from_bytes_with_nul(s.as_bytes()).unwrap())
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        State { values }
    }

    pub fn values(&self) -> &[U32; N] {
        &self.values
    }

    pub fn recover_seed_array1(&mut self, solver: &mut Solver) -> [U32; 1] {
        let mult1 = U32::from(1664525);
        let mult2 = U32::from(1566083941);

        let state = &mut *self.values;
        // `twist` discards the low bits of state[0]. Check that the MSB is set.
        solver.assert(&(&state[0] & 0x80000000).equals(&U32::from(0x80000000)));
        state[1] = (&state[1] + 1) ^ ((&state[N - 1] ^ (&state[N - 1] >> 30)) * &mult2);
        for i in (2..N).rev() {
            state[i] =
                (&state[i] + (i as u32)) ^ ((&state[i - 1] ^ (&state[i - 1] >> 30)) * &mult2);
        }

        let init = crate::Random::from_u32(19650218).state;

        // Start with state[N - 1], where the key is the only unknown.
        let key0 = (&state[N - 1]
            - (init[N - 1] ^ ((&state[N - 2] ^ (&state[N - 2] >> 30)) * &mult1)))
            .simplify();

        state[0] = U32::from(init[0]);
        state[1] = (&state[1] - &key0) ^ ((&state[N - 1] ^ (&state[N - 1] >> 30)) * &mult1);
        for i in (1..N - 1).rev() {
            let test_key0 =
                &state[i] - (init[i] ^ ((&state[i - 1] ^ (&state[i - 1] >> 30)) * &mult1));
            solver.assert(&test_key0.equals(&key0));
        }
        [key0]
    }

    pub fn twist(&mut self) {
        let state = &mut *self.values;
        for i in 0..N {
            state[i] = (&state[(i + M) % N]
                ^ ((&state[i] & 0x80000000) >> 1)
                ^ ((&state[(i + 1) % N] & 0x7ffffffe) >> 1)
                ^ ((&state[(i + 1) % N] & 0x1) * 0x9908b0df))
                .simplify();
        }
    }

    pub fn untwist(&mut self) {
        let state = &mut *self.values;
        for i in (0..N).rev() {
            let x = &state[i] ^ &state[(i + M) % N];
            let msb = (&x << 1) & 0x80000000;
            let lsb = &x >> 31;
            let mid = ((x ^ (&lsb * 0x9908b0df)) << 1) & 0x7ffffffe;
            state[i] &= 0x7fffffff;
            state[i] |= msb;
            state[(i + 1) % N] &= 0x80000000;
            state[(i + 1) % N] |= mid | lsb;
        }
    }

    pub fn untemper(mut x: U32) -> U32 {
        x ^= &x >> 18;
        x ^= (&x << 15) & 0x2fc60000;
        x ^= (&x << 15) & 0xc0000000;
        x ^= (&x << 7) & 0x00001680;
        x ^= (&x << 7) & 0x000c4000;
        x ^= (&x << 7) & 0x0d200000;
        x ^= (&x << 7) & 0x90000000;
        x ^= &x >> 11;
        x ^= &x >> 22;
        x.simplify()
    }
}

#[cfg(test)]
mod tests {
    use crate::global_z3::SatResult;

    use super::*;

    #[test]
    fn abstract_matches_concrete() {
        let seed = 123;
        let len = N - 5;
        let mut forward_rand = crate::Random::from_array1([seed]);
        let mut sym_rand = Random::new();
        for _ in 0..len {
            let v = crate::Random::untemper(forward_rand.next_u32());
            let eq = &sym_rand.next_u32().equals(&U32::from(v));
            sym_rand.solver().assert(eq);
        }
        assert_eq!(sym_rand.solver().check(), SatResult::Sat);
        let model = sym_rand.solver().get_model().unwrap();
        let seed_eval = sym_rand.seed()[0].eval(&model, true).unwrap();
        assert_eq!(seed_eval.as_const().unwrap(), seed);
    }
}
