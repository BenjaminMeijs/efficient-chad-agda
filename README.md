# Efficient CHAD: Agda formalisation

CHAD [[1]][chad1] is an automatic differentiation (AD) algorithm in the form of a code transformation.
That is to say, it takes a program (in a functional language) that computes some function from real numbers to real numbers, and produces a different program that not only computes the original result of the input program, but also its derivative.
(The input program is allowed to have other arguments or results than just real numbers or structures/arrays of real numbers, but these will not be active for differentiation.)

In the paper [[2]][arxiv2], the authors optimise the CHAD code transformation to make it attain this goal and provide a proof that the desired complexity is indeed attained.
This repository contains an Agda formalisation of this complexity proof.

In this project, we further extended the Agda formalisation of CHAD with a correctness proof.
Specifically, we prove that the derivative according to CHAD is equivalent to semantic differentiation.


## Building the proof

Type checking the code = checking the proof, because of how Agda works.
We use Agda 2.7.0.1 with [standard-library](https://github.com/agda/agda-stdlib/releases/tag/v1.7.2) version 2.1.1.


## Structure of the code

The **specification** is given in the directory `./spec` and `spec.agda`.
The `spec.linear-types` module sets up some definitions about the monoids that we use (our use of "linear" in this repository refers to monoid structures, not resource-linearity as in Rust, Linear Haskell etc.); `spec.LACM` then defines an abstract _local accumulation monad_ with some declared complexity properties (that the implementation in Agda does not satisfy because it lacks mutability, but a proper implementation is easily written in e.g. Haskell); finally, `spec.agda` gives the term language we operate on, its semantics and cost model (`eval`) and the CHAD code transformation.

The **complexity proof** from [[2]][arxiv2] can be found in `./cost/chad-cost.agda`.

The **correctness proof** of this project can be found in the folder `./correctness`.  
`chad-equiv-dsem.agda` contains the actual correctness proof. `dsem.agda` contains the embedding of semantic differentiation using postulates. `spec.agda` contains a dense representation in which semantic equality implies intensional equality (and trivially, vice versa). Our concept of syntactic differentiability is defined in `dsyn-defefined.agda`. `chad-ctg-zero.agda` and `chad-preserves-compatibility.agda` contain importent theorems about CHAD used wihtin the correctness proof. Likewise, `./lemmas` contains lemmas used by the correctness proof.

[chad1]: https://dl.acm.org/doi/10.1145/3527634
[arxiv2]: https://arxiv.org/abs/2307.05738

## Source
This project is part of the master's thesis 'Formal Correctness Proofs for Efficient
CHAD' by Benjamin Meijs.