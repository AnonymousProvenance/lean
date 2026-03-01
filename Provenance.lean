/- Various semirings -/
import Provenance.Semirings.Bool
import Provenance.Semirings.BoolFunc
import Provenance.Semirings.How
import Provenance.Semirings.Lukasiewicz
import Provenance.Semirings.MinMax
import Provenance.Semirings.Nat
import Provenance.Semirings.Tropical
import Provenance.Semirings.Viterbi
import Provenance.Semirings.Which
import Provenance.Semirings.Why

/-!
This Lean4 library aims at providing formal definitions and proofs
relevant for provenance semirings.

- `Provenance.SemiringWithMonus` contains the definition of a semiring with monus (or m-semiring), along with some classical and useful theorems
- We include proofs that some common provenance m-semirings are indeed m-semirings:
  - `Provenance.Semirings.Bool`: the Boolean m-semiring
  - `Provenance.Semirings.BoolFunc`: the Bool[X] m-semiring of Boolean functions over a set X of Boolean variables
  - `Provenance.Semirings.How`: the ℕ[X] m-semiring of multivariate polynomials with natural integer coefficients, sometimes called the How[X] m-semiring; it is the m-semiring extension of the universal provenance semiring
  - `Provenance.Semirings.Lukasiewicz`: the Łukasiewicz semiring
  - `Provenance.Semirings.MinMax`: the min-max semiring over any bounded linear order, such as the security semiring or (the dual of) the fuzzy semiring
  - `Provenance.Semirings.Nat`: the counting m-semiring
  - `Provenance.Semirings.Tropical`: the tropical m-semiring (for any linearly ordered commutative monoid with an additively absorbing ⊤ element, e.g., natural integers or reals with ∞ as ⊤)
  - `Provenance.Semirings.Viterbi`: the Viterbi m-semiring
  - `Provenance.Semirings.Which`: the Which[X] m-semiring (also called lineage or Lin[X])
  - `Provenance.Semirings.Why`: the Why[X] m-semiring
-/
