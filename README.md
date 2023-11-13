# Mersenne Untwisted: Fully Reversing MT19937

A reverse implementation of the MT19937 [Mersenne Twister](http://www.math.sci.hiroshima-u.ac.jp/m-mat/MT/emt.html)
pseudorandom number generator, that can recover the seed in some cases, when
given the desired outputs.

The source tree has several implementations and experiments. It has not been
reorganized as a cohesive API, and is currently presented as-is.

- Implementations:
  - `random.rs`: Forwards implementation using concrete `u32` values.
  - `reverse.rs`: Reverse implementation using concrete `u32` values. Reverses
    `random.rs`.
  - `symbolic_reverse.rs`: Hybrid forwards and reverse implementation using Z3
    values.
  - `ascii96.rs`: Adaptor for working with the program encoding of the [Seed](https://esolangs.org/wiki/Seed)
    programming language, concretely and symbolically.
- Libraries:
  - `global_z3/`: Alternative high-level Z3 API for Rust, which uses a
    thread-local context and statically typed bitvector sizes, designed to be
    easier to use than the [`z3`](https://crates.io/crates/z3) crate.
- Experiments and analysis:
  - `smt.rs`: Attempt at using Z3 to solve for the seed with the only forward
    algorithm.
  - `bitblast/`: A symbolic `u32` type, that uses 32 Z3 `bool` values and
    implements bitwise and arithmetic ops using hand-rolled bit-blasting.
  - `symbolic.rs`: A symbolic version of `twist`, that tracks word-level
    dependence as a graph.
  - `symbolic_bits/`: A symbolic version of `twist`, that tracks bit-level
    dependence as a graph, which assisted in the creation of `untwist`.
    Supersedes `symbolic.rs`.

This references the algorithms of the 2002 version of MT19937, [mt19937ar](https://github.com/thaliaarchi/mt19937-archive/tree/mt19937ar-2002),
for which I have [reconstructed](https://github.com/thaliaarchi/mt19937-archive)
a revision history, as well as its use in Python [`random`](https://github.com/python/cpython/blob/v3.12.0/Modules/_randommodule.c).
