use std::ffi::CStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use z3_sys::{
    Z3_ast, Z3_ast_to_string, Z3_context, Z3_dec_ref, Z3_get_numeral_uint64, Z3_inc_ref,
    Z3_mk_bv_sort, Z3_mk_bvadd, Z3_mk_bvand, Z3_mk_bvlshr, Z3_mk_bvmul, Z3_mk_bvneg, Z3_mk_bvnot,
    Z3_mk_bvor, Z3_mk_bvshl, Z3_mk_bvsub, Z3_mk_bvudiv, Z3_mk_bvurem, Z3_mk_bvxor, Z3_mk_const,
    Z3_mk_eq, Z3_mk_string_symbol, Z3_mk_unsigned_int64, Z3_model_eval,
};

use crate::global_z3::{ctx, Bool, Model, Z3_fmt};

/// A version of [`z3::ast::BV`] with size 32, that uses a thread-local context.
pub struct U32 {
    pub(super) ast: Z3_ast,
}

impl U32 {
    #[inline]
    pub fn new(name: &CStr) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, Self::var(ctx, name))
    }

    /// Unwrapped version of [`z3::ast::BV::new_const`] with a string symbol.
    fn var(ctx: Z3_context, name: &CStr) -> Z3_ast {
        unsafe {
            let sort = Z3_mk_bv_sort(ctx, 32);
            let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
            Z3_mk_const(ctx, sym, sort)
        }
    }

    /// Unwrapped version of [`z3::ast::BV::from_u64`].
    fn lit(ctx: Z3_context, n: u32) -> Z3_ast {
        unsafe {
            let sort = Z3_mk_bv_sort(ctx, 32);
            Z3_mk_unsigned_int64(ctx, n as u64, sort)
        }
    }

    #[inline]
    pub(super) fn wrap(ctx: Z3_context, ast: Z3_ast) -> Self {
        unsafe { Z3_inc_ref(ctx, ast) };
        U32 { ast }
    }

    #[inline]
    pub fn equals(&self, rhs: &U32) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_eq(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn as_const(&self) -> Option<u32> {
        let mut tmp = 0;
        if unsafe { Z3_get_numeral_uint64(ctx(), self.ast, &mut tmp) } {
            Some(tmp.try_into().unwrap())
        } else {
            None
        }
    }

    #[inline]
    pub fn eval(&self, model: &Model, model_completion: bool) -> Option<U32> {
        let ctx = ctx();
        let mut out: Z3_ast = self.ast;
        if unsafe { Z3_model_eval(ctx, model.model, self.ast, model_completion, &mut out) } {
            Some(Self::wrap(ctx, out))
        } else {
            None
        }
    }
}

impl From<u32> for U32 {
    #[inline]
    fn from(n: u32) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, Self::lit(ctx, n))
    }
}

impl Clone for U32 {
    #[inline]
    fn clone(&self) -> Self {
        Self::wrap(ctx(), self.ast)
    }
}

impl Drop for U32 {
    #[inline]
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(ctx(), self.ast) };
    }
}

impl Debug for U32 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for U32 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Z3_fmt(f, self.ast, Z3_ast_to_string)
    }
}

macro_rules! impl_binop(($Op:ident, $Lhs:ty, $Rhs:ty, $op:ident, $func:ident) => {
    impl $Op<$Rhs> for $Lhs {
        type Output = U32;

        #[inline]
        fn $op(self, rhs: $Rhs) -> Self::Output {
            $func(ctx(), self.ast, rhs.ast)
        }
    }
});
macro_rules! impl_binop_const_rhs(($Op:ident, $Lhs:ty, $op:ident, $func:ident) => {
    impl $Op<u32> for $Lhs {
        type Output = U32;

        #[inline]
        fn $op(self, rhs: u32) -> Self::Output {
            let ctx = ctx();
            $func(ctx, self.ast, U32::lit(ctx, rhs))
        }
    }
});
macro_rules! impl_binop_const_lhs(($Op:ident, $Rhs:ty, $op:ident, $func:ident) => {
    impl $Op<$Rhs> for u32 {
        type Output = U32;

        #[inline]
        fn $op(self, rhs: $Rhs) -> Self::Output {
            let ctx = ctx();
            $func(ctx, U32::lit(ctx, self), rhs.ast)
        }
    }
});
macro_rules! impl_binop_assign(($OpAssign:ident, $Rhs:ty, $op_assign:ident, $func:ident) => {
    impl $OpAssign<$Rhs> for U32 {
        #[inline]
        fn $op_assign(&mut self, rhs: $Rhs) {
            *self = $func(ctx(), self.ast, rhs.ast)
        }
    }
});
macro_rules! impl_binop_assign_const_rhs(($OpAssign:ident, $op_assign:ident, $func:ident) => {
    impl $OpAssign<u32> for U32 {
        #[inline]
        fn $op_assign(&mut self, rhs: u32) {
            let ctx = ctx();
            *self = $func(ctx, self.ast, U32::lit(ctx, rhs))
        }
    }
});
macro_rules! binop(($Op:ident, $OpAssign:ident, $op:ident, $op_assign:ident, $func:ident, $z3_func:ident) => {
    impl_binop!($Op, U32, U32, $op, $func);
    impl_binop!($Op, U32, &U32, $op, $func);
    impl_binop!($Op, &U32, U32, $op, $func);
    impl_binop!($Op, &U32, &U32, $op, $func);
    impl_binop_const_rhs!($Op, U32, $op, $func);
    impl_binop_const_rhs!($Op, &U32, $op, $func);
    impl_binop_const_lhs!($Op, U32, $op, $func);
    impl_binop_const_lhs!($Op, &U32, $op, $func);
    impl_binop_assign!($OpAssign, U32, $op_assign, $func);
    impl_binop_assign!($OpAssign, &U32, $op_assign, $func);
    impl_binop_assign_const_rhs!($OpAssign, $op_assign, $func);

    #[inline]
    fn $func(ctx: Z3_context, lhs: Z3_ast, rhs: Z3_ast) -> U32 {
        unsafe { U32::wrap(ctx, $z3_func(ctx, lhs, rhs)) }
    }
});

macro_rules! impl_unop(($Op:ident, $Lhs:ty, $op:ident, $func:ident) => {
    impl $Op for $Lhs {
        type Output = U32;

        #[inline]
        fn $op(self) -> Self::Output {
            $func(ctx(), self.ast)
        }
    }
});
macro_rules! unop(($Op:ident, $op:ident, $func:ident, $z3_func:ident) => {
    impl_unop!($Op, U32, $op, $func);
    impl_unop!($Op, &U32, $op, $func);

    #[inline]
    fn $func(ctx: Z3_context, x: Z3_ast) -> U32 {
        unsafe { U32::wrap(ctx, $z3_func(ctx, x)) }
    }
});

binop!(Add, AddAssign, add, add_assign, u32_add, Z3_mk_bvadd);
binop!(Sub, SubAssign, sub, sub_assign, u32_sub, Z3_mk_bvsub);
binop!(Mul, MulAssign, mul, mul_assign, u32_mul, Z3_mk_bvmul);
binop!(Div, DivAssign, div, div_assign, u32_div, Z3_mk_bvudiv);
binop!(Rem, RemAssign, rem, rem_assign, u32_rem, Z3_mk_bvurem);
binop!(
    BitAnd,
    BitAndAssign,
    bitand,
    bitand_assign,
    u32_and,
    Z3_mk_bvand
);
binop!(BitOr, BitOrAssign, bitor, bitor_assign, u32_or, Z3_mk_bvor);
binop!(
    BitXor,
    BitXorAssign,
    bitxor,
    bitxor_assign,
    u32_xor,
    Z3_mk_bvxor
);
binop!(Shl, ShlAssign, shl, shl_assign, u32_shl, Z3_mk_bvshl);
binop!(Shr, ShrAssign, shr, shr_assign, u32_shr, Z3_mk_bvlshr);
unop!(Neg, neg, u32_neg, Z3_mk_bvneg);
unop!(Not, not, u32_not, Z3_mk_bvnot);
