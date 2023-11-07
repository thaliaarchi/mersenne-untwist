use std::fmt::{self, Debug, Display, Formatter};

use z3_sys::{
    Z3_context, Z3_mk_solver, Z3_solver, Z3_solver_assert, Z3_solver_check, Z3_solver_dec_ref,
    Z3_solver_inc_ref, Z3_solver_to_string, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF,
};

use crate::global_z3::{ctx, Bool, Model, Z3_fmt};

pub struct Solver {
    pub(super) solver: Z3_solver,
}

/// Result of a satisfiability query.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    /// The query is unsatisfiable.
    Unsat,
    /// The query was interrupted, timed out or otherwise failed.
    Unknown,
    /// The query is satisfiable.
    Sat,
}

impl Solver {
    pub fn new() -> Self {
        let ctx = ctx();
        Self::wrap(ctx, unsafe { Z3_mk_solver(ctx) })
    }

    #[inline]
    fn wrap(ctx: Z3_context, solver: Z3_solver) -> Self {
        unsafe { Z3_solver_inc_ref(ctx, solver) };
        Solver { solver }
    }

    #[inline]
    pub fn assert(&self, b: &Bool) {
        unsafe { Z3_solver_assert(ctx(), self.solver, b.ast) };
    }

    #[inline]
    pub fn check(&self) -> SatResult {
        match unsafe { Z3_solver_check(ctx(), self.solver) } {
            Z3_L_FALSE => SatResult::Unsat,
            Z3_L_UNDEF => SatResult::Unknown,
            Z3_L_TRUE => SatResult::Sat,
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn get_model(&self) -> Option<Model> {
        Model::new(self)
    }
}

impl Default for Solver {
    #[inline]
    fn default() -> Self {
        Solver::new()
    }
}

impl Clone for Solver {
    #[inline]
    fn clone(&self) -> Self {
        Self::wrap(ctx(), self.solver)
    }
}

impl Drop for Solver {
    #[inline]
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(ctx(), self.solver) };
    }
}

impl Debug for Solver {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Solver {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Z3_fmt(f, self.solver, Z3_solver_to_string)
    }
}
