use std::ffi::CStr;
use std::fmt::{self, Formatter};

use z3_sys::{Z3_context, Z3_mk_config, Z3_mk_context_rc, Z3_set_error_handler};

pub use bool::*;
pub use bv::*;
pub use model::*;
pub use solver::*;

mod bool;
mod bv;
mod model;
mod solver;

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

#[allow(non_snake_case)]
fn Z3_fmt<T>(
    f: &mut Formatter<'_>,
    v: T,
    to_string: unsafe extern "C" fn(Z3_context, T) -> *const i8,
) -> fmt::Result {
    let p = unsafe { to_string(ctx(), v) };
    if p.is_null() {
        return Err(fmt::Error);
    }
    match unsafe { CStr::from_ptr(p) }.to_str() {
        Ok(s) => f.write_str(s),
        Err(_) => Err(fmt::Error),
    }
}
