use std::ffi::CStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use z3_sys::{
    Z3_ast, Z3_ast_to_string, Z3_context, Z3_dec_ref, Z3_get_numeral_uint64, Z3_inc_ref,
    Z3_mk_bv_sort, Z3_mk_bvadd, Z3_mk_bvand, Z3_mk_bvlshr, Z3_mk_bvmul, Z3_mk_bvneg, Z3_mk_bvnot,
    Z3_mk_bvor, Z3_mk_bvshl, Z3_mk_bvsub, Z3_mk_bvudiv, Z3_mk_bvuge, Z3_mk_bvugt, Z3_mk_bvule,
    Z3_mk_bvult, Z3_mk_bvurem, Z3_mk_bvxor, Z3_mk_const, Z3_mk_eq, Z3_mk_ite, Z3_mk_string_symbol,
    Z3_mk_unsigned_int64, Z3_model_eval, Z3_simplify,
};

use crate::global_z3::{ctx, Bool, Model, Z3_fmt};

/// An unsigned version of [`z3::ast::BV`] with size `N`, that uses a
/// thread-local context.
pub struct BV<const N: usize> {
    pub(super) ast: Z3_ast,
}

pub type U8 = BV<8>;
pub type U16 = BV<16>;
pub type U32 = BV<32>;
pub type U64 = BV<64>;

impl<const N: usize> BV<N> {
    #[inline]
    pub fn new(name: &CStr) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, mk_bv_var(ctx, name, N))
    }

    #[inline]
    pub fn from_u64(n: u64) -> Option<Self> {
        if N < 64 && n >> N != 0 {
            None
        } else {
            let ctx = ctx();
            Some(Self::wrap(ctx, mk_bv_lit(ctx, n, N)))
        }
    }

    #[inline]
    pub(super) fn wrap(ctx: Z3_context, ast: Z3_ast) -> Self {
        unsafe { Z3_inc_ref(ctx, ast) };
        BV { ast }
    }

    #[inline]
    pub fn equals(&self, rhs: &Self) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_eq(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn lt(&self, rhs: &Self) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_bvult(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn le(&self, rhs: &Self) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_bvule(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn gt(&self, rhs: &Self) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_bvugt(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn ge(&self, rhs: &Self) -> Bool {
        let ctx = ctx();
        Bool::wrap(ctx, unsafe { Z3_mk_bvuge(ctx, self.ast, rhs.ast) })
    }

    #[inline]
    pub fn ite(b_if: &Bool, v_then: &Self, v_else: &Self) -> Self {
        let ctx = ctx();
        let ast = unsafe { Z3_mk_ite(ctx, b_if.ast, v_then.ast, v_else.ast) };
        BV::wrap(ctx, ast)
    }

    #[inline]
    pub fn eval(&self, model: &Model, model_completion: bool) -> Option<Self> {
        let ctx = ctx();
        let mut out: Z3_ast = self.ast;
        if unsafe { Z3_model_eval(ctx, model.model, self.ast, model_completion, &mut out) } {
            Some(Self::wrap(ctx, out))
        } else {
            None
        }
    }

    #[inline]
    pub fn simplify(&self) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, unsafe { Z3_simplify(ctx, self.ast) })
    }

    #[inline]
    pub fn cast<const M: usize>(self) -> BV<M> {
        if M > 64 {
            panic!("size above 64 not supported");
        }
        let ast = if M < N {
            let mut bv = BV::<64> { ast: self.ast };
            bv &= (1u64 << M) - 1;
            bv.ast
        } else {
            self.ast
        };
        BV { ast }
    }
}

impl BV<8> {
    #[inline]
    pub fn as_const(&self) -> Option<u8> {
        get_const(ctx(), self.ast).map(|n| n.try_into().unwrap())
    }
}

impl BV<16> {
    #[inline]
    pub fn as_const(&self) -> Option<u16> {
        get_const(ctx(), self.ast).map(|n| n.try_into().unwrap())
    }
}

impl BV<32> {
    #[inline]
    pub fn as_const(&self) -> Option<u32> {
        get_const(ctx(), self.ast).map(|n| n.try_into().unwrap())
    }
}

impl BV<64> {
    #[inline]
    pub fn as_const(&self) -> Option<u64> {
        get_const(ctx(), self.ast)
    }
}

/// Unwrapped version of [`z3::ast::BV::new_const`] with a string symbol.
#[inline]
fn mk_bv_var(ctx: Z3_context, name: &CStr, size: usize) -> Z3_ast {
    unsafe {
        let sort = Z3_mk_bv_sort(ctx, size as _);
        let sym = Z3_mk_string_symbol(ctx, name.as_ptr());
        Z3_mk_const(ctx, sym, sort)
    }
}

/// Unwrapped version of [`z3::ast::BV::from_u64`].
#[inline]
fn mk_bv_lit<T: Into<u64>>(ctx: Z3_context, n: T, size: usize) -> Z3_ast {
    unsafe {
        let sort = Z3_mk_bv_sort(ctx, size as _);
        Z3_mk_unsigned_int64(ctx, n.into(), sort)
    }
}

fn get_const(ctx: Z3_context, ast: Z3_ast) -> Option<u64> {
    let mut n = 0;
    if unsafe { Z3_get_numeral_uint64(ctx, ast, &mut n) } {
        Some(n)
    } else {
        None
    }
}

impl From<u8> for BV<8> {
    #[inline]
    fn from(n: u8) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, mk_bv_lit(ctx, n, 8))
    }
}

impl From<u16> for BV<16> {
    #[inline]
    fn from(n: u16) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, mk_bv_lit(ctx, n, 16))
    }
}

impl From<u32> for BV<32> {
    #[inline]
    fn from(n: u32) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, mk_bv_lit(ctx, n, 32))
    }
}

impl From<u64> for BV<64> {
    #[inline]
    fn from(n: u64) -> Self {
        let ctx = ctx();
        Self::wrap(ctx, mk_bv_lit(ctx, n, 64))
    }
}

impl<const N: usize> Clone for BV<N> {
    #[inline]
    fn clone(&self) -> Self {
        Self::wrap(ctx(), self.ast)
    }
}

impl<const N: usize> Drop for BV<N> {
    #[inline]
    fn drop(&mut self) {
        unsafe { Z3_dec_ref(ctx(), self.ast) };
    }
}

impl<const N: usize> Debug for BV<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<const N: usize> Display for BV<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Z3_fmt(f, self.ast, Z3_ast_to_string)
    }
}

macro_rules! ref_ty(
    (ref $ty:ty) => { & $ty };
    (owned $ty:ty) => { $ty };
);
macro_rules! impl_binop(($Op:ident, $lhs_ref:ident, $rhs_ref:ident, $op:ident, $func:ident) => {
    impl<const N: usize> $Op<ref_ty!($rhs_ref BV<N>)> for ref_ty!($lhs_ref BV<N>) {
        type Output = BV<N>;

        #[inline]
        fn $op(self, rhs: ref_ty!($rhs_ref BV<N>)) -> Self::Output {
            let ctx = ctx();
            unsafe { BV::wrap(ctx, $func(ctx, self.ast, rhs.ast)) }
        }
    }
});
macro_rules! impl_binop_const_rhs(($Op:ident, $lhs_ref:ident, [$($N:literal / $Rhs:ty),+], $op:ident, $func:ident) => {
    $(impl $Op<$Rhs> for ref_ty!($lhs_ref BV<$N>) {
        type Output = BV<$N>;

        #[inline]
        fn $op(self, rhs: $Rhs) -> Self::Output {
            let ctx = ctx();
            unsafe { BV::wrap(ctx, $func(ctx, self.ast, mk_bv_lit(ctx, rhs, $N))) }
        }
    })+
});
macro_rules! impl_binop_const_lhs(($Op:ident, [$($N:literal / $Lhs:ty),+], $rhs_ref:ident, $op:ident, $func:ident) => {
    $(impl $Op<ref_ty!($rhs_ref BV<$N>)> for $Lhs {
        type Output = BV<$N>;

        #[inline]
        fn $op(self, rhs: ref_ty!($rhs_ref BV<$N>)) -> Self::Output {
            let ctx = ctx();
            unsafe { BV::wrap(ctx, $func(ctx, mk_bv_lit(ctx, self, $N), rhs.ast)) }
        }
    })+
});
macro_rules! impl_binop_usize_rhs(($Op:ident, $lhs_ref:ident, $op:ident, $func:ident) => {
    impl<const N: usize> $Op<usize> for ref_ty!($lhs_ref BV<N>) {
        type Output = BV<N>;

        #[inline]
        fn $op(self, rhs: usize) -> Self::Output {
            let ctx = ctx();
            unsafe { BV::wrap(ctx, $func(ctx, self.ast, mk_bv_lit(ctx, rhs as u64, N))) }
        }
    }
});
macro_rules! impl_binop_assign(($OpAssign:ident, $rhs_ref:ident, $op_assign:ident, $func:ident) => {
    impl<const N: usize> $OpAssign<ref_ty!($rhs_ref BV<N>)> for BV<N> {
        #[inline]
        fn $op_assign(&mut self, rhs: ref_ty!($rhs_ref BV<N>)) {
            let ctx = ctx();
            *self = unsafe { BV::wrap(ctx, $func(ctx, self.ast, rhs.ast)) };
        }
    }
});
macro_rules! impl_binop_assign_const_rhs(($OpAssign:ident, [$($N:literal / $Rhs:ty),+], $op_assign:ident, $func:ident) => {
    $(impl $OpAssign<$Rhs> for BV<$N> {
        #[inline]
        fn $op_assign(&mut self, rhs: $Rhs) {
            let ctx = ctx();
            *self = unsafe { BV::wrap(ctx, $func(ctx, self.ast, mk_bv_lit(ctx, rhs, $N))) };
        }
    })+
});
macro_rules! impl_binop_assign_usize_rhs(($OpAssign:ident, $op_assign:ident, $func:ident) => {
    impl<const N: usize> $OpAssign<usize> for BV<N> {
        #[inline]
        fn $op_assign(&mut self, rhs: usize) {
            let ctx = ctx();
            *self = unsafe { BV::wrap(ctx, $func(ctx, self.ast, mk_bv_lit(ctx, rhs as u64, N))) };
        }
    }
});
macro_rules! binop_base(($Op:ident, $OpAssign:ident, $op:ident, $op_assign:ident, $func:ident) => {
    impl_binop!($Op, owned, owned, $op, $func);
    impl_binop!($Op, owned, ref, $op, $func);
    impl_binop!($Op, ref, owned, $op, $func);
    impl_binop!($Op, ref, ref, $op, $func);
    impl_binop_assign!($OpAssign, owned, $op_assign, $func);
    impl_binop_assign!($OpAssign, ref, $op_assign, $func);
});
macro_rules! binop_typed(($Op:ident, $OpAssign:ident, $op:ident, $op_assign:ident, $func:ident) => {
    impl_binop_const_rhs!($Op, owned, [8/u8, 16/u16, 32/u32, 64/u64], $op, $func);
    impl_binop_const_rhs!($Op, ref, [8/u8, 16/u16, 32/u32, 64/u64], $op, $func);
    impl_binop_const_lhs!($Op, [8/u8, 16/u16, 32/u32, 64/u64], owned, $op, $func);
    impl_binop_const_lhs!($Op, [8/u8, 16/u16, 32/u32, 64/u64], ref, $op, $func);
    impl_binop_assign_const_rhs!($OpAssign, [8/u8, 16/u16, 32/u32, 64/u64], $op_assign, $func);
});
macro_rules! binop_usize(($Op:ident, $OpAssign:ident, $op:ident, $op_assign:ident, $func:ident) => {
    impl_binop_usize_rhs!($Op, owned, $op, $func);
    impl_binop_usize_rhs!($Op, ref, $op, $func);
    impl_binop_assign_usize_rhs!($OpAssign, $op_assign, $func);
});
macro_rules! binop(
    ($Op:ident, $OpAssign:ident, $op:ident, $op_assign:ident, $func:ident, T) => {
        binop_base!($Op, $OpAssign, $op, $op_assign, $func);
        binop_typed!($Op, $OpAssign, $op, $op_assign, $func);
    };
    ($Op:ident, $OpAssign:ident, $op:ident, $op_assign:ident, $func:ident, usize) => {
        binop_base!($Op, $OpAssign, $op, $op_assign, $func);
        binop_usize!($Op, $OpAssign, $op, $op_assign, $func);
    };
);

macro_rules! impl_unop(($Op:ident, $lhs_ref:ident, $op:ident, $func:ident) => {
    impl<const N: usize> $Op for ref_ty!($lhs_ref BV<N>) {
        type Output = BV<N>;

        #[inline]
        fn $op(self) -> Self::Output {
            let ctx = ctx();
            unsafe { BV::wrap(ctx, $func(ctx, self.ast)) }
        }
    }
});
macro_rules! unop(($Op:ident, $op:ident, $func:ident) => {
    impl_unop!($Op, owned, $op, $func);
    impl_unop!($Op, ref, $op, $func);
});

binop!(Add, AddAssign, add, add_assign, Z3_mk_bvadd, T);
binop!(Sub, SubAssign, sub, sub_assign, Z3_mk_bvsub, T);
binop!(Mul, MulAssign, mul, mul_assign, Z3_mk_bvmul, T);
binop!(Div, DivAssign, div, div_assign, Z3_mk_bvudiv, T);
binop!(Rem, RemAssign, rem, rem_assign, Z3_mk_bvurem, T);
binop!(BitAnd, BitAndAssign, bitand, bitand_assign, Z3_mk_bvand, T);
binop!(BitOr, BitOrAssign, bitor, bitor_assign, Z3_mk_bvor, T);
binop!(BitXor, BitXorAssign, bitxor, bitxor_assign, Z3_mk_bvxor, T);
binop!(Shl, ShlAssign, shl, shl_assign, Z3_mk_bvshl, usize);
binop!(Shr, ShrAssign, shr, shr_assign, Z3_mk_bvlshr, usize);
unop!(Neg, neg, Z3_mk_bvneg);
unop!(Not, not, Z3_mk_bvnot);
