use z3::{
    ast::{Ast, BV},
    Context,
};

use crate::{Random, N};

pub struct AbstractRandom<'ctx> {
    ctx: &'ctx Context,
    state: Box<[BV<'ctx>; N]>,
    index: usize,
}

macro_rules! num(($ctx:expr, $n:expr) => {
    BV::from_u64($ctx, $n as u64, 32)
});
#[allow(unused_macros)]
macro_rules! var(($ctx:expr, $name:expr) => {
    BV::new_const($ctx, $name, 32)
});

impl<'ctx> AbstractRandom<'ctx> {
    pub fn from_u32(ctx: &'ctx Context, seed: &BV<'ctx>) -> AbstractRandom<'ctx> {
        let mult = &num!(ctx, 1812433253);
        let shift = &num!(ctx, 30);
        let mut state = Vec::with_capacity(N);
        state.push(seed.clone());
        for i in 1..N {
            let prev = &state[i - 1];
            let v = (prev ^ prev.bvlshr(shift)) * mult + num!(ctx, i as u32);
            state.push(v)
        }
        let state = state.try_into().unwrap();
        AbstractRandom::from_state(ctx, state)
    }

    pub fn from_u32_const(ctx: &'ctx Context, seed: u32) -> AbstractRandom<'ctx> {
        let state = Random::from_u32(seed)
            .state()
            .map(|n| num!(ctx, n))
            .try_into()
            .unwrap();
        AbstractRandom::from_state(ctx, state)
    }

    pub fn from_array1(ctx: &'ctx Context, key0: &BV<'ctx>) -> AbstractRandom<'ctx> {
        let mult1 = &num!(ctx, 1664525);
        let mult2 = &num!(ctx, 1566083941);
        let shift = &num!(ctx, 30);

        let mut state = AbstractRandom::from_u32_const(ctx, 19650218).state;

        for i in 1..N {
            let prev = &state[i - 1];
            state[i] = (&state[i] ^ ((prev ^ prev.bvlshr(shift)) * mult1)) + key0;
        }
        let last = &state[N - 1];
        state[1] = (&state[1] ^ ((last ^ last.bvlshr(shift)) * mult1)) + key0;

        for i in 2..N {
            let prev = &state[i - 1];
            state[i] = (&state[i] ^ ((prev ^ (prev.bvlshr(shift))) * mult2)) - num!(ctx, i as u32);
        }
        let last = &state[N - 1];
        state[1] = (&state[1] ^ ((last ^ last.bvlshr(shift)) * mult2)) - &num!(ctx, 1);

        state[0] = num!(ctx, 0x80000000);
        AbstractRandom::from_state(ctx, state)
    }

    pub fn from_state(ctx: &'ctx Context, state: Box<[BV<'ctx>; N]>) -> Self {
        AbstractRandom {
            ctx,
            state,
            index: N,
        }
    }

    pub fn next_u32<'s>(&'s mut self) -> &'s BV<'ctx> {
        const M: usize = 397;
        let matrix_a = &num!(self.ctx, 0x9908b0df);
        let upper_mask = &num!(self.ctx, 0x80000000);
        let lower_mask = &num!(self.ctx, 0x7fffffff);
        let zero = &num!(self.ctx, 0);
        let one = &num!(self.ctx, 1);

        let state = &mut self.state;

        if self.index == N {
            for k in 0..N - M {
                let y = (&state[k] & upper_mask) | (&state[k + 1] & lower_mask);
                let mag = (&y & one)._eq(zero).ite(zero, matrix_a);
                state[k] = &state[k + M] ^ y.bvlshr(one) ^ mag;
            }
            for k in N - M..N - 1 {
                let y = (&state[k] & upper_mask) | (&state[k + 1] & lower_mask);
                let mag = (&y & one)._eq(zero).ite(zero, matrix_a);
                state[k] = &state[k - (N - M)] ^ y.bvlshr(one) ^ mag;
            }
            let y = (&state[N - 1] & upper_mask) | (&state[0] & lower_mask);
            let mag = (&y & one)._eq(zero).ite(zero, matrix_a);
            state[N - 1] = &state[M - 1] ^ y.bvlshr(one) ^ mag;

            self.index = 0;
        }

        let y = &mut state[self.index];
        self.index += 1;

        *y ^= y.bvlshr(&num!(self.ctx, 11));
        *y ^= (&*y << &num!(self.ctx, 7)) & &num!(self.ctx, 0x9d2c5680);
        *y ^= (&*y << &num!(self.ctx, 15)) & &num!(self.ctx, 0xefc60000);
        *y ^= y.bvlshr(&num!(self.ctx, 18));
        &*y
    }
}

#[cfg(test)]
mod tests {
    use z3::{Config, SatResult, Solver};

    use super::*;

    #[test]
    fn abstract_matches_concrete() {
        let seed = 123;

        let ctx = Context::new(&Config::new());
        let mut arand = AbstractRandom::from_u32_const(&ctx, seed);
        let x_var = arand.next_u32();
        let solver = Solver::new(&ctx);
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let x_bv = model.eval(x_var, true).unwrap();
        let x: u32 = x_bv.as_u64().unwrap().try_into().unwrap();

        let mut rand = Random::from_u32(seed);
        assert_eq!(x, rand.next_u32());
    }

    #[test]
    #[ignore = "too slow"]
    fn solve_seed() {
        let ctx = Context::new(&Config::new());
        let seed_var = var!(&ctx, "seed");
        let mut arand = AbstractRandom::from_u32(&ctx, &seed_var);
        let x = arand.next_u32();
        let solver = Solver::new(&ctx);
        solver.assert(&x._eq(&num!(&ctx, 0xb24bcdfe)));
        assert_eq!(solver.check(), SatResult::Sat);
        let model = solver.get_model().unwrap();
        let seed_bv = model.eval(&seed_var, true).unwrap();
        let seed: u32 = seed_bv.as_u64().unwrap().try_into().unwrap();
        assert_eq!(seed, 123);
    }
}
