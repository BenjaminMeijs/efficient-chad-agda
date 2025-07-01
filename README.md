# Efficient Higher-order CHAD

CHAD [[1]][chad1] is an automatic differentiation (AD) algorithm in the form of a code transformation.
That is to say, it takes a program (in a functional language) that computes some function from real numbers to real numbers, and produces a different program that not only computes the original result of the input program, but also its derivative.
(The input program is allowed to have other arguments or results than just real numbers or structures/arrays of real numbers, but these will not be active for differentiation.)


For this project, we extended the pre-existing Agda implementation from [[2]][arxiv2].
Specifically, we extended the first-order source language to a higher-order language.
Additionally, we made the foundation for a correctness proof of this extension.


## Structure of the code

The **specification** of CHAD is given in `spec.agda` and the folder `./spec`.
The `spec.linear-types` module sets up some definitions about the monoids that we use (our use of "linear" in this repository refers to monoid structures, not resource-linearity as in Rust, Linear Haskell etc.); `spec.LACM` then defines an abstract _local accumulation monad_ with some declared complexity properties (that the implementation in Agda does not satisfy because it lacks mutability, but a proper implementation is easily written in e.g. Haskell); finally, `spec.agda` gives the term language we operate on, its semantics and cost model (`eval`), and the CHAD code transformation as we modified it (`chad`).

The foundation of the **correctness proof** is found in the folder `./HO-correctness`.
`HO-chad-equiv-dsem` contains the actual correctness criterion and its proof,
    for functions from vector-like values to vector-like values, the derivative according to CHAD is equivalent to semantic differentiation.
Semantic differentiation is encoded through postulates in `dsem.adga`.
This proof is based on the definition of a logical relation (`logical-relation.agda`) and a proof that CHAD satisfies the logical relation (`fundamental-lemma.agda`).
Proving the fundamental lemma is beyond the scope of this project.

`dense-rep.agda` contains a dense representation, in which semantic equality implies intensional equality (and trivially, vice versa). Lastly, `./HO-correctness/lemmas` contains lemmas useful for the correctness proof.


[chad1]: https://dl.acm.org/doi/10.1145/3527634
[arxiv2]: https://arxiv.org/abs/2307.05738


## Source
This project is part of the master's thesis 'Formal Correctness Proofs for Efficient CHAD' by Benjamin Meijs
