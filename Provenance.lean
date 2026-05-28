/- Semirings with monus and concrete instances -/
import Provenance.SemiringWithMonus

import Provenance.Semirings.Bool
import Provenance.Semirings.BoolFunc
import Provenance.Semirings.How
import Provenance.Semirings.IntervalUnion
import Provenance.Semirings.Lukasiewicz
import Provenance.Semirings.MinMax
import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical
import Provenance.Semirings.Viterbi
import Provenance.Semirings.Which
import Provenance.Semirings.Why

/- HAVING algebraic identities -/
import Provenance.Having

/- Probability distributions over Boolean variables and the independence lemma -/
import Provenance.Probability

/- HAVING aggregate-comparison probability identities under contributor
   independence -/
import Provenance.HavingProbability

/- Algorithms (HAVING enumeration) -/
import Provenance.Algorithms.CompOp
import Provenance.Algorithms.CountEnum
import Provenance.Algorithms.SumDP

/-!
This Lean 4 library provides formal definitions and proofs relevant for
provenance in databases, following the semiring framework of
[Green, Karvounarakis & Tannen][green2007provenance] and
[Green & Tannen][green2017provenance].

## Contents

**Core theory**

- `Provenance.SemiringWithMonus` – definition of a *semiring with monus*
  (m-semiring), the algebraic structure underlying annotated database
  semantics, together with general theorems about it.
- `Provenance.Having` – algebraic identities behind `HAVING (count)`
  aggregate provenance: include/exclude recurrences for the JOIN and
  possible-world expressions and the upward-expansion bound.
- `Provenance.Probability` – intensional probability semantics for
  `BoolFunc X`-annotated data: probability distribution over Boolean
  valuations, probability of a Boolean function, and the independence
  lemma `Pr(f * g) = Pr(f) * Pr(g)` for `f`, `g` with disjoint variable
  supports.
- `Provenance.HavingProbability` – probability identities for evaluating
  `HAVING`-style aggregate comparisons under contributor independence:
  the MAX / MIN factorisation formulas (`funcProb_maxLeOnNonempty` /
  `funcProb_minGeOnNonempty`) and the COUNT / SUM Poisson-binomial-style
  recurrences (`countMass_insert_zero` / `countMass_insert_succ` /
  `sumMass_insert_of_le` / `sumMass_insert_of_lt`).

**Algorithms**

- `Provenance.Algorithms.CompOp` – shared comparison-operator type used
  by the HAVING enumeration algorithms.
- `Provenance.Algorithms.CountEnum` – enumeration of valid possible
  worlds for `HAVING count op C` predicates: definitions of
  `combinations`, `addExact`, and `countEnum`, together with the
  correctness theorem `countEnum_correct`.
- `Provenance.Algorithms.SumDP` – subset-sum enumeration of valid
  possible worlds for `HAVING sum(t) op C` predicates: definition of
  `sumExact` and `sumDP`, together with the correctness theorem
  `sumDP_correct`.

**Concrete m-semirings** (`Provenance.Semirings.*`)

- `Provenance.Semirings.Bool` – the Boolean m-semiring `𝔹`.
- `Provenance.Semirings.BoolFunc` – the Boolean-function m-semiring `𝔹[X]`.
- `Provenance.Semirings.Why` – the Why[X] m-semiring (sets of witness sets).
- `Provenance.Semirings.Which` – the Which[X] m-semiring (lineage / Lin[X]).
- `Provenance.Semirings.How` – the ℕ[X] m-semiring of multivariate
  polynomials; the universal provenance semiring.
- `Provenance.Semirings.Nat` – the counting m-semiring `ℕ`.
- `Provenance.Semirings.Tropical` – the tropical m-semiring (min-plus)
  over `ℕ ∪ {∞}`, `ℚ ∪ {∞}`, or `ℝ ∪ {∞}`; the `ℝ` instance is also used
  as a counterexample showing that the absorptive hypothesis of
  `Having.F_eq_S` is genuinely required (idempotent + `⊗`-over-`⊖`
  distributive is not enough).
- `Provenance.Semirings.Viterbi` – the Viterbi m-semiring (max-times) over
  `[0,1]`.
- `Provenance.Semirings.MinMax` – the min-max semiring over any bounded
  linear order (security / access-control semiring and dual fuzzy
  semiring).
- `Provenance.Semirings.Lukasiewicz` – the Łukasiewicz (fuzzy logic)
  m-semiring over `ℚ ∩ [0,1]`.
- `Provenance.Semirings.IntervalUnion` – finite unions of intervals over a
  dense linear order, used for temporal databases.

## References

* [Green, Karvounarakis & Tannen, *Provenance Semirings*][green2007provenance]
* [Geerts & Poggi, *On database query languages for K-relations*][geerts2010database]
* [Green & Tannen, *The Semiring Framework for Database Provenance*][green2017provenance]
-/
