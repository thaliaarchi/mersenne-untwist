mod bool;
mod u32;

pub use bool::*;
pub use u32::*;
use z3_sys::{Z3_context, Z3_mk_config, Z3_mk_context_rc, Z3_set_error_handler};

thread_local! {
    static CTX: Z3_context = init_ctx();
}

/// Unwrapped version of [`z3::Context::new`] and [`c3::Config::new`];
#[inline(never)]
fn init_ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let ctx = Z3_mk_context_rc(cfg);
        Z3_set_error_handler(ctx, None);
        ctx
    }
}

#[inline]
fn ctx() -> Z3_context {
    CTX.with(|&ctx| ctx)
}
