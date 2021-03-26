# CHAD: Combinatory Homomorphic Automatic Differentiation
![chad](./chad-logo.svg)

This repo contains a reference implementation of CHAD.

CHAD is a method for reverse and forward mode automatic differentiation on expressive functional languages. It performs AD as a compositional, type-safe source code transformation that transforms each language primitive to its (transposed) derivative. This code transformation is homomorphic in the sense of being a structure preserving functor -- in fact, this homomorphism property forces the definitions of CHAD to be what they are. As a consequence, CHAD admits a straightforward correctness proof that shows that it computes the correct (transposed) derivative of any composite program, provided that the (transposed) derivatives of all language primitives are implemented correctly. This compositionality makes CHAD easy to extend with new language features. CHAD is prettiest when the source language is first transformed to categorical combinators.

CHAD was introduced in [[1]](https://arxiv.org/abs/2007.05283), which was, in turn, inspired by the ideas in [[2]](https://arxiv.org/abs/1804.00746). [[3]](https://openreview.net/forum?id=ryxuz9SzDB) turns out to give a similar treatment of AD of higher order functions as the homomorphic definitions dictated by CHAD.

## Example programs
A few example programs are available in [Examples.hs](./Examples.hs). These can be tested by first building the library (`stack build`) and then opening the file in GHCi (`stack ghci Examples.hs`).

