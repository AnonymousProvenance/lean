# Provenance in databases, in Lean 4

A Lean 4 formalization of *database provenance* in the semiring framework of
Green, Karvounarakis and Tannen: relations whose tuples are annotated with
values from a semiring, an annotated relational algebra with difference and
aggregation, the provenance-aware query rewriting of Sen et al. (ICDE 2026),
and the provenance semantics of `HAVING` aggregate comparisons.

This repository is the anonymized companion of a paper submission: it contains
the material that paper links to. **API documentation:**
<https://anonymousprovenance.github.io/Provenance.html>.

## What is formalized

Everything below is proved in the library. `lake build` is the test suite:
there is no separate one, and the development is `sorry`-free.

| Result | Module | Entry point |
| --- | --- | --- |
| m-semirings: monus from its Galois connection, the `δ` support operator, homomorphisms | `Provenance/SemiringWithMonus.lean` | `SemiringWithMonus`, `SemiringWithMonusHom` |
| thirteen concrete provenance m-semirings: `𝔹`, `𝔹[X]`, `Why[X]`, `Lin[X]`, `ℕ[X]`, `ℕ`, tropical, Viterbi, min-max, Łukasiewicz, a five-element chain, intervals and interval unions | `Provenance/Semirings/` | one file per semiring |
| annotated relational algebra with difference, and its provenance-aware rewriting into a plain query over `T ⊕ K` | `Provenance/QueryRewriting.lean` | `Query.rewriting_valid` |
| query evaluation commutes with any m-semiring homomorphism on `RA⁺(∖)` | `Provenance/QueryAnnotatedDatabaseHom.lean` | `Query.evaluateAnnotated_hom` |
| data-part adequacy of the annotated semantics against the plain one | `Provenance/QueryAdequacy.lean` | `Nat.counterexample_diff_adequacy` bounds it |
| probabilistic query evaluation: random worlds and the possible-worlds reading of `𝔹[X]` annotations | `Provenance/Probability.lean` | `randomWorld_evaluateAnnotated` |
| Boolean provenance circuits, read-once and deterministic-decomposable correctness | `Provenance/Circuit.lean` | `Circuit` |
| a **kind-indexed general query syntax** whose three column kinds (regular values, aggregate tokens, provenance values) make the scope restrictions on aggregate results static typing rather than side conditions | `Provenance/AggQuery.lean` | `AggQuery` |
| symbolic aggregate tokens and their semantics, invariant under permutations of tied group elements | `Provenance/AggValue.lean`, `Provenance/AggValueCongr.lean` | `AggValue`, `AggValue.predProv_congr` |
| the rewriting stated natively on that syntax, the rewriting of a bare `GROUP BY`, the `HAVING` site for a predicate mixing aggregate and regular atoms, and their **compositional closure** over arbitrary token-bearing plans | `Provenance/AggQueryRewriting.lean`, `Provenance/AggQueryGroupRewriting.lean`, `Provenance/AggQueryClosure.lean` | `AggQuery.rewritesTo_valid` |
| hom commutation and random-world commutation of the general evaluator | `Provenance/AggQueryHom.lean`, `Provenance/AggQueryProbability.lean` | `AggQuery.evaluateAnnotated_hom` |
| provenance of `HAVING`: its possible-world semantics, the algebraic identities behind counting aggregates, the corresponding probability identities under independence, a scan-computable form for `MIN`/`MAX`/`PICKFIRST`, and the enumeration algorithms with their correctness | `Provenance/HavingSemantics.lean`, `Provenance/Having.lean`, `Provenance/HavingProbability.lean`, `Provenance/HavingMinMax.lean`, `Provenance/Algorithms/` | `Having.havingProv` |
| query-level correctness of the fused `HAVING` operator against the JOIN-based rewriting, and `decide`-checked counterexamples showing its hypotheses are needed | `Provenance/HavingQueryCorrectness.lean`, `Provenance/HavingQueryCounterexamples.lean` | `Query.joinCount_correct` |
| complexity: non-zero `HAVING SUM` provenance is NP-complete in data complexity, with hardness by a first-order reduction and a size-honest encoding of concrete groups | `Provenance/HavingComplexity.lean` | `havingSumProv_ne_zero_iff`, `havingSumNonzeroHow_faithful` |

## Layers

The library is layered, and the core ripples downward when touched:

1. **Algebra** – `SemiringWithMonus` and the concrete semirings under
   `Provenance/Semirings/`.
2. **Data** – `Database.lean` (tuples, relations, plain databases) and
   `AnnotatedDatabase.lean` (the same, annotated in an m-semiring `K`).
3. **Queries** – `Query.lean` (the classical syntax and its plain semantics),
   `QueryAnnotatedDatabase.lean` (the annotated semantics),
   `QueryRewriting.lean` (the rewriting into `T ⊕ K`).
4. **The general framework** – the `AggQuery*` family: the kind-indexed syntax,
   its evaluator, and the aggregation and `HAVING` results. This is the primary
   interface; the classical layer remains the proven engine several of its
   results reuse internally.
5. **Applications** – probability, circuits, algorithms, complexity.

## Building

The toolchain in `lean-toolchain` must match the pinned Mathlib version.

```
lake exe cache get   # fetch the Mathlib build cache
lake build           # build the whole library; this is the test suite
```

Besides Mathlib, the library depends on the
[descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity/releases/tag/v1.2.0)
library, used to state the complexity results; Lake resolves one Mathlib per
workspace, so both sit on the same pin.

Building the documentation is a separate project, `docbuild/`:

```
cd docbuild && lake build Provenance:docs
```

The HTML tree is then in `docbuild/.lake/build/doc`.

One caveat: this package sets `backward.isDefEq.respectTransparency false`,
because its carriers (`Tuple`, `Relation`, `Database`, …) are deliberately
opaque `def`s that instance search must nevertheless see through.
