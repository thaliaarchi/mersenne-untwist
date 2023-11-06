//! An implementation of the MT19937 [Mersenne Twister](http://www.math.sci.hiroshima-u.ac.jp/m-mat/MT/emt.html)
//! pseudorandom number generator.
//!
//! It is ported from the 2002 version, [mt19937ar](https://github.com/thaliaarchi/mt19937-archive/tree/mt19937ar-2002).

mod random;
mod smt;

pub use random::*;
pub use smt::*;
