# Lean4 formalization of some provenance notions

This repository includes some Lean4 formal definitions and proofs
relevant for provenance in databases.

- We include proofs that some common provenance m-semirings are indeed
  m-semirings:
  - [Bool.lean](Provenance/Semirings/Bool.lean): the Boolean m-semiring
  - [BoolFunc.lean](Provenance/Semirings/BoolFunc.lean): the Bool\[X\] m-semiring of Boolean functions over a set X of Boolean variables
  - [How.lean](Provenance/Semirings/How.lean): the ℕ\[X\] m-semiring of multivariate polynomials with natural integer coefficients, sometimes called the How\[X\] m-semiring; it is the m-semiring extension of the universal provenance semiring
  - [Lukasiewicz.lean](Provenance/Semirings/Lukasiewicz.lean): the Łukasiewicz semiring
  - [MinMax.lean](Provenance/Semirings/MinMax.lean): the min-max semiring over any bounded linear order, such as the security semiring or (the dual of) the fuzzy semiring
  - [Nat.lean](Provenance/Semirings/Nat.lean): the counting m-semiring
  - [Tropical.lean](Provenance/Semirings/Tropical.lean): the tropical m-semiring (for any linearly ordered commutative monoid with an additively absorbing ⊤ element, e.g., natural integers or reals with ∞ as ⊤)
  - [Viterbi.lean](Provenance/Semirings/Viterbi.lean): the Viterbi m-semiring
  - [Which.lean](Provenance/Semirings/Which.lean): the Which\[X\] m-semiring (also called lineage or Lin\[X\])
  - [Why.lean](Provenance/Semirings/Why.lean): the Why\[X\] m-semiring
