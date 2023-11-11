use std::ffi::CStr;

use crate::{
    global_z3::{Solver, U32},
    M, N,
};

#[derive(Clone, Debug)]
pub struct State {
    reverse: Box<[U32; N]>,
    forward: Box<[U32; N]>,
    index: usize,
    solver: Solver,
}

impl State {
    pub fn new() -> Self {
        let vars: Box<[U32; N]> = (0..N)
            .map(|i| {
                let s = format!("s{i}\0");
                U32::new(CStr::from_bytes_with_nul(s.as_bytes()).unwrap())
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let mut state = State {
            reverse: vars.clone(),
            forward: vars,
            index: 0,
            solver: Solver::new(),
        };
        state.untwist();
        // TODO: Call recover_seed_array1
        state
    }

    pub fn push_u32(&mut self, x: U32) {
        self.solver
            .assert(&self.forward[self.index].equals(&State::untemper(x)));
        self.index += 1;
        if self.index >= N {
            self.twist();
            self.index = 0;
        }
    }

    fn twist(&mut self) {
        let state = &mut *self.forward;
        for i in 0..N {
            state[i] = &state[(i + M) % N]
                ^ ((&state[i] & 0x80000000) >> 1)
                ^ ((&state[(i + 1) % N] & 0x7ffffffe) >> 1)
                ^ ((&state[(i + 1) % N] & 0x1) * 0x9908b0df);
        }
    }

    fn untwist(&mut self) {
        let state = &mut *self.reverse;
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

    fn untemper(mut x: U32) -> U32 {
        x ^= &x >> 18;
        x ^= (&x << 15) & 0x2fc60000;
        x ^= (&x << 15) & 0xc0000000;
        x ^= (&x << 7) & 0x00001680;
        x ^= (&x << 7) & 0x000c4000;
        x ^= (&x << 7) & 0x0d200000;
        x ^= (&x << 7) & 0x90000000;
        x ^= &x >> 11;
        x ^= &x >> 22;
        x
    }
}

impl Extend<U32> for State {
    fn extend<T: IntoIterator<Item = U32>>(&mut self, iter: T) {
        for x in iter.into_iter() {
            self.push_u32(x);
        }
    }
}
