use std::ffi::CStr;

use z3_sys::{
    Z3_ast, Z3_context, Z3_dec_ref, Z3_inc_ref, Z3_mk_bool_sort, Z3_mk_const, Z3_mk_false,
    Z3_mk_string_symbol, Z3_mk_true,
};

use crate::global_z3::ctx;

/// A version of [`z3::ast::Bool`], that uses a thread-local context.
pub struct Bool {
    ast: Z3_ast,
}

impl Bool {
    #[inline]
    pub fn new(name: &CStr) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, Self::var(ctx, name))
    }

    /// Unwrapped version of [`z3::ast::Bool::new_const`] with a string symbol.
    fn var(ctx: Z3_context, name: &CStr) -> Z3_ast {
        unsafe {
            let sort = Z3_mk_bool_sort(ctx);
            let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
            Z3_mk_const(ctx, sym, sort)
        }
    }

    /// Unwrapped version of [`z3::ast::Bool::from_bool`].
    fn lit(ctx: Z3_context, b: bool) -> Z3_ast {
        unsafe {
            if b {
                Z3_mk_true(ctx)
            } else {
                Z3_mk_false(ctx)
            }
        }
    }

    #[inline]
    fn wrap(ctx: Z3_context, ast: Z3_ast) -> Self {
        unsafe {
            Z3_inc_ref(ctx, ast);
        }
        Bool { ast }
    }
}

impl From<bool> for Bool {
    #[inline]
    fn from(b: bool) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, Self::lit(ctx, b))
    }
}

impl Clone for Bool {
    #[inline]
    fn clone(&self) -> Self {
        Self::wrap(ctx(), self.ast)
    }
}

impl Drop for Bool {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(ctx(), self.ast);
        }
    }
}
