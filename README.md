# Lean 4 formalization of some provenance notions

This repository contains Lean 4 formal definitions and proofs relevant
for provenance in databases, in the semiring framework of Green,
Karvounarakis, and Tannen.

## Contents

- [`Provenance.SemiringWithMonus`](Provenance/SemiringWithMonus.lean) –
  definition of a *semiring with monus* (m-semiring) and its general
  theorems.
- [`Provenance.Having`](Provenance/Having.lean) – algebraic identities
  behind `HAVING (count)` aggregate provenance: include/exclude
  recurrences for the JOIN-based and possible-world expressions plus the
  upward-expansion bound.
- [`Provenance.Probability`](Provenance/Probability.lean) – probability
  distributions over Boolean valuations, the probability of a Boolean
  function, and the independence lemma `Pr(f * g) = Pr(f) · Pr(g)` for
  `f`, `g` with disjoint variable supports.
- [`Provenance.HavingProbability`](Provenance/HavingProbability.lean) –
  probability identities for evaluating `HAVING`-style aggregate
  comparisons under contributor independence (MAX / MIN factorisation,
  COUNT / SUM Poisson-binomial-style recurrences).
- [`Provenance.Algorithms`](Provenance/Algorithms/) – correctness
  theorems for the enumeration algorithms (`SumDP`, `CountEnum`) used
  to evaluate `HAVING sum(t) op C` and `HAVING count op C` provenance.
- Proofs that common provenance m-semirings are indeed m-semirings:
  - [`Bool`](Provenance/Semirings/Bool.lean), [`BoolFunc`](Provenance/Semirings/BoolFunc.lean) – the Boolean and Boolean-function m-semirings.
  - [`How`](Provenance/Semirings/How.lean) – the universal `ℕ[X]` m-semiring.
  - [`Nat`](Provenance/Semirings/Nat.lean) – the counting m-semiring `ℕ`.
  - [`Tropical`](Provenance/Semirings/Tropical.lean) – the tropical
    (min-plus) m-semiring over `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, or `ℝ ∪ {∞}`; the
    `ℝ` instance also serves as a counterexample to `Having.F_eq_S`
    without the absorptive hypothesis.
  - [`Viterbi`](Provenance/Semirings/Viterbi.lean) – the Viterbi
    (max-times) m-semiring over `[0,1]`.
  - [`MinMax`](Provenance/Semirings/MinMax.lean) – the min-max semiring
    over any bounded linear order (security / fuzzy semirings).
  - [`Lukasiewicz`](Provenance/Semirings/Lukasiewicz.lean) – the
    Łukasiewicz (fuzzy logic) m-semiring over `ℚ ∩ [0,1]`.
  - [`Which`](Provenance/Semirings/Which.lean), [`Why`](Provenance/Semirings/Why.lean) – the Which[X] (lineage) and Why[X] m-semirings.
  - [`IntervalUnion`](Provenance/Semirings/IntervalUnion.lean) – finite
    unions of intervals, for temporal databases.

## Building

```
lake exe cache get
lake build
```

Requires the Lean 4 toolchain version pinned in
[`lean-toolchain`](lean-toolchain).
