use std::fmt::{self, Debug, Display, Formatter};

use z3_sys::{
    Z3_context, Z3_model, Z3_model_dec_ref, Z3_model_inc_ref, Z3_model_to_string,
    Z3_solver_get_model,
};

use crate::global_z3::{ctx, Solver, Z3_fmt};

pub struct Model {
    pub(super) model: Z3_model,
}

impl Model {
    pub fn new(solver: &Solver) -> Option<Self> {
        unsafe {
            let ctx = ctx();
            let model = Z3_solver_get_model(ctx, solver.solver);
            if !model.is_null() {
                Some(Self::wrap(ctx, model))
            } else {
                None
            }
        }
    }

    #[inline]
    fn wrap(ctx: Z3_context, model: Z3_model) -> Self {
        unsafe { Z3_model_inc_ref(ctx, model) };
        Model { model }
    }
}

impl Clone for Model {
    #[inline]
    fn clone(&self) -> Self {
        Self::wrap(ctx(), self.model)
    }
}

impl Drop for Model {
    #[inline]
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(ctx(), self.model) };
    }
}

impl Debug for Model {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Model {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Z3_fmt(f, self.model, Z3_model_to_string)
    }
}
