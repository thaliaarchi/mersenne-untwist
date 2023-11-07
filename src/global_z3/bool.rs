use std::ffi::CStr;
use std::fmt::{self, Debug, Display, Formatter};

use z3_sys::{
    Z3_ast, Z3_ast_to_string, Z3_context, Z3_dec_ref, Z3_get_bool_value, Z3_inc_ref, Z3_mk_and,
    Z3_mk_bool_sort, Z3_mk_const, Z3_mk_eq, Z3_mk_false, Z3_mk_iff, Z3_mk_ite, Z3_mk_or,
    Z3_mk_string_symbol, Z3_mk_true, Z3_model_eval, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF,
};

use crate::global_z3::{ctx, Model, Z3_fmt, U32};

/// A version of [`z3::ast::Bool`], that uses a thread-local context.
pub struct Bool {
    pub(super) ast: Z3_ast,
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
    pub(super) fn wrap(ctx: Z3_context, ast: Z3_ast) -> Self {
        unsafe { Z3_inc_ref(ctx, ast) };
        Bool { ast }
    }

    #[inline]
    pub fn and(&self, rhs: &Self) -> Self {
        let ctx = ctx();
        let args = [self.ast, rhs.ast];
        let ast = unsafe { Z3_mk_and(ctx, 2, args.as_ptr()) };
        Bool::wrap(ctx, ast)
    }

    #[inline]
    pub fn or(&self, rhs: &Self) -> Self {
        let ctx = ctx();
        let args = [self.ast, rhs.ast];
        let ast = unsafe { Z3_mk_or(ctx, 2, args.as_ptr()) };
        Bool::wrap(ctx, ast)
    }

    pub fn all<I: IntoIterator<Item = Bool>>(iter: I) -> Self {
        let ctx = ctx();
        let args = iter.into_iter().map(|b| b.ast).collect::<Vec<_>>();
        let ast = unsafe { Z3_mk_and(ctx, args.len() as u32, args.as_ptr()) };
        Bool::wrap(ctx, ast)
    }

    pub fn any<I: IntoIterator<Item = Bool>>(iter: I) -> Self {
        let ctx = ctx();
        let args = iter.into_iter().map(|b| b.ast).collect::<Vec<_>>();
        let ast = unsafe { Z3_mk_or(ctx, args.len() as u32, args.as_ptr()) };
        Bool::wrap(ctx, ast)
    }

    #[inline]
    pub fn ite(&self, v_then: &U32, v_else: &U32) -> U32 {
        let ctx = ctx();
        let ast = unsafe { Z3_mk_ite(ctx, self.ast, v_then.ast, v_else.ast) };
        U32::wrap(ctx, ast)
    }

    #[inline]
    pub fn iff(&self, rhs: &Bool) -> Bool {
        let ctx = ctx();
        let ast = unsafe { Z3_mk_iff(ctx, self.ast, rhs.ast) };
        Bool::wrap(ctx, ast)
    }

    #[inline]
    pub fn equals(&self, rhs: &Bool) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_eq(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn as_const(&self) -> Option<bool> {
        match unsafe { Z3_get_bool_value(ctx(), self.ast) } {
            Z3_L_TRUE => Some(true),
            Z3_L_FALSE => Some(false),
            Z3_L_UNDEF => None,
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn eval(&self, model: &Model, model_completion: bool) -> Option<Bool> {
        let ctx = ctx();
        let mut out: Z3_ast = self.ast;
        if unsafe { Z3_model_eval(ctx, model.model, self.ast, model_completion, &mut out) } {
            Some(Self::wrap(ctx, out))
        } else {
            None
        }
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
        unsafe { Z3_dec_ref(ctx(), self.ast) };
    }
}

impl Debug for Bool {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Bool {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Z3_fmt(f, self.ast, Z3_ast_to_string)
    }
}
