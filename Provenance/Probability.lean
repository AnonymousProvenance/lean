import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Linarith

import Provenance.Semirings.Bool
import Provenance.Semirings.BoolFunc

/-!
# Probability distributions over Boolean variables

Given a finite set `X` of Boolean variables and an assignment `Pr : X → ℚ`
of probabilities (with values in `[0, 1]`), we extend `Pr` to:

* a probability distribution over valuations `v : X → Bool`, assuming the
  variables are independent: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`;
* a probability of a Boolean function `f : BoolFunc X`, defined as the sum of
  `Pr(v)` over satisfying valuations: `Pr(f) = ∑_{v ⊨ f} Pr(v)`.

We also develop the standard `BoolFunc.DependsOn` notion of support and prove
the independence lemma `Pr(f * g) = Pr(f) · Pr(g)` when `f` and `g` depend on
disjoint variable supports.

## Main definitions

* `ProbAssignment X` – a probability assignment to each variable, bundled
  with `0 ≤ Pr(x) ≤ 1`.
* `ProbAssignment.valProb` – `Pr(v)` for a single valuation `v : X → Bool`.
* `ProbAssignment.funcProb` – `Pr(f)` for a Boolean function `f : BoolFunc X`.
* `BoolFunc.DependsOn` – `f` depends only on a `Finset` of variables.

## Main results

* `ProbAssignment.valProb_nonneg`, `valProb_le_one`, `sum_valProb_eq_one` –
  basic properties of the valuation distribution.
* `ProbAssignment.funcProb_zero`, `funcProb_one`, `funcProb_nonneg`,
  `funcProb_le_one`, `funcProb_congr` – basic properties of `Pr(f)`.
* `ProbAssignment.funcProb_var` – `Pr(var i) = Pr(i)`.
* `ProbAssignment.funcProb_sub_self_const_one` – `Pr(1 - f) = 1 - Pr(f)`.
* `ProbAssignment.funcProb_mul_disjoint` – the **independence lemma**:
  `Pr(f * g) = Pr(f) * Pr(g)` whenever `f`, `g` depend on disjoint variable
  supports.
* `ProbAssignment.funcProb_add_eq` – inclusion-exclusion at OR:
  `Pr(f + g) = Pr(f) + Pr(g) - Pr(f * g)`.
-/

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x

omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is non-negative. -/
private lemma valProb_factor_nonneg (v : X → Bool) (x : X) :
    0 ≤ (if v x then P.prob x else 1 - P.prob x) := by
  by_cases hv : v x
  · simp [hv]; exact P.prob_nonneg x
  · simp [hv]
    have := P.prob_le_one x
    linarith

omit [Fintype X] [DecidableEq X] in
/-- Each factor `(if v x then P.prob x else 1 - P.prob x)` is at most `1`. -/
private lemma valProb_factor_le_one (v : X → Bool) (x : X) :
    (if v x then P.prob x else 1 - P.prob x) ≤ 1 := by
  by_cases hv : v x
  · simp [hv]; exact P.prob_le_one x
  · simp [hv]
    have := P.prob_nonneg x
    linarith

omit [DecidableEq X] in
theorem valProb_nonneg (v : X → Bool) : 0 ≤ P.valProb v :=
  Finset.prod_nonneg (fun x _ => P.valProb_factor_nonneg v x)

omit [DecidableEq X] in
theorem valProb_le_one (v : X → Bool) : P.valProb v ≤ 1 := by
  unfold valProb
  calc ∏ x, (if v x then P.prob x else 1 - P.prob x)
      ≤ ∏ _x : X, (1 : ℚ) :=
        Finset.prod_le_prod
          (fun x _ => P.valProb_factor_nonneg v x)
          (fun x _ => P.valProb_factor_le_one v x)
    _ = 1 := by simp

omit [Fintype X] [DecidableEq X] in
/-- For any `x : X`, `Pr(x) + (1 - Pr(x)) = 1`: summing the two cases of the
factor at `x` over `Bool` gives `1`. -/
private lemma sum_factor_at (x : X) :
    ∑ b : Bool, (if b then P.prob x else 1 - P.prob x) = 1 := by
  -- Bool's univ is {false, true}; enumerate explicitly.
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
      Finset.sum_singleton]
  simp

/-- The valuations form a probability distribution: `∑ v, Pr(v) = 1`. -/
theorem sum_valProb_eq_one : ∑ v : X → Bool, P.valProb v = 1 := by
  -- Reduce ∑_v ∏_x f(x, v x) to ∏_x ∑_b f(x, b) via Fintype.prod_sum, then
  -- close via `sum_factor_at`.
  have hps :
      (∏ x : X, ∑ b : Bool, (if b then P.prob x else 1 - P.prob x))
        = ∑ v : X → Bool, ∏ x : X, (if v x then P.prob x else 1 - P.prob x) :=
    Fintype.prod_sum (fun (x : X) (b : Bool) => if b then P.prob x else 1 - P.prob x)
  unfold valProb
  rw [← hps]
  simp_rw [P.sum_factor_at]
  simp


/-- Probability of a Boolean function: `Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : BoolFunc X) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

theorem funcProb_nonneg (f : BoolFunc X) : 0 ≤ P.funcProb f := by
  unfold funcProb
  apply Finset.sum_nonneg
  intro v _
  by_cases hv : f v
  · simp [hv]; exact P.valProb_nonneg v
  · simp [hv]

/-- `Pr(f) ≤ ∑_v Pr(v) = 1`. -/
theorem funcProb_le_one (f : BoolFunc X) : P.funcProb f ≤ 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : f v
  · simp [hv]
  · simp [hv]; exact P.valProb_nonneg v

/-- `Pr(0) = 0`: the constant-false function has probability zero. -/
theorem funcProb_zero : P.funcProb (0 : BoolFunc X) = 0 := by
  unfold funcProb
  apply Finset.sum_eq_zero
  intro v _
  show (if (0 : BoolFunc X) v then P.valProb v else 0) = 0
  -- (0 : BoolFunc X) v = false
  have h : (0 : BoolFunc X) v = false := rfl
  rw [h]
  simp

/-- `Pr(1) = 1`: the constant-true function has probability one. -/
theorem funcProb_one : P.funcProb (1 : BoolFunc X) = 1 := by
  rw [← P.sum_valProb_eq_one]
  unfold funcProb
  apply Finset.sum_congr rfl
  intro v _
  have h : (1 : BoolFunc X) v = true := rfl
  rw [h]
  simp

/-- Pointwise-equal Boolean functions have equal probabilities. -/
theorem funcProb_congr {f g : BoolFunc X} (h : ∀ v, f v = g v) :
    P.funcProb f = P.funcProb g := by
  unfold funcProb
  apply Finset.sum_congr rfl
  intro v _
  rw [h v]

/-- Reformulation: `Pr(f)` as a sum over the satisfying valuations. -/
theorem funcProb_eq_filter_sum (f : BoolFunc X) :
    P.funcProb f = ∑ v ∈ Finset.univ.filter (fun v => f v = true), P.valProb v := by
  unfold funcProb
  rw [← Finset.sum_filter]

end ProbAssignment

/-! ### `BoolFunc.DependsOn`: support of a Boolean function -/

/-- `f` depends only on the variables in `S`: any two valuations agreeing
on `S` produce the same value. This is the standard notion of "support". -/
def BoolFunc.DependsOn {X : Type} (f : BoolFunc X) (S : Finset X) : Prop :=
  ∀ v₁ v₂ : X → Bool, (∀ x ∈ S, v₁ x = v₂ x) → f v₁ = f v₂

/-! ### Auxiliary `funcProb` lemmas -/

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- `Pr(var i) = Pr(i)`: the probability of the single-variable Boolean function
equals the variable's own probability. Proved by reorganising the sum
`∑_v if v i then valProb v else 0` as a product `∏_y h_y(v y)` and applying
`Fintype.prod_sum` (the same swap used in `sum_valProb_eq_one`). -/
theorem funcProb_var (i : X) :
    P.funcProb (BoolFunc.var i) = P.prob i := by
  -- Local helper: factor at y, depending on v y.
  -- For y = i: contributes `b ↦ if b then Pr(i) else 0` (kills the `v i = false` case).
  -- For y ≠ i: contributes the usual `P̃_y(b)`.
  let h : X → Bool → ℚ := fun y b =>
    if y = i then (if b then P.prob i else 0)
    else (if b then P.prob y else 1 - P.prob y)
  -- The product ∏_y h y (v y) equals (if v i then valProb v else 0).
  have hprod : ∀ v : X → Bool,
      (∏ y, h y (v y)) = if (v i : Bool) then P.valProb v else 0 := by
    intro v
    by_cases hvi : v i = true
    · -- v i = true: factor at i is P.prob i = P̃_i(true), so the product reduces to valProb v.
      simp only [hvi, if_true]
      unfold valProb
      apply Finset.prod_congr rfl
      intro y _
      by_cases hy : y = i
      · subst hy
        simp only [h, if_pos rfl, hvi, if_true]
      · simp only [h, if_neg hy]
    · -- v i = false: factor at i is 0, so the product vanishes.
      have hvi' : v i = false := by
        cases hv : v i
        · rfl
        · exact absurd hv hvi
      simp only [hvi']
      apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
      simp only [h, if_pos rfl, hvi']
      rfl
  -- Per-variable sum: contributes `P.prob i` at `y = i`, and `1` elsewhere.
  have hsum : ∀ y, (∑ b, h y b) = if y = i then P.prob i else 1 := by
    intro y
    by_cases hy : y = i
    · subst hy
      simp only [h, if_pos rfl]
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
          Finset.sum_singleton]
      simp
    · simp only [h, if_neg hy]
      have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
          Finset.sum_singleton]
      simp
  -- Apply Fintype.prod_sum (∏∑ = ∑∏) in reverse.
  have hswap : (∑ v : X → Bool, ∏ y, h y (v y)) = ∏ y, ∑ b, h y b :=
    (Fintype.prod_sum h).symm
  -- Goal: rewrite funcProb's sum to match.
  show (∑ v : X → Bool, if (BoolFunc.var i v : Bool) then P.valProb v else 0) = P.prob i
  have hvar : ∀ v : X → Bool, BoolFunc.var i v = v i := fun _ => rfl
  have hstep1 : (∑ v : X → Bool, if (BoolFunc.var i v : Bool) then P.valProb v else 0)
              = ∑ v : X → Bool, ∏ y, h y (v y) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [hvar v, ← hprod v]
  rw [hstep1, hswap]
  -- Now: ∏ y, ∑ b, h y b = P.prob i
  have hstep2 : (∏ y, ∑ b, h y b) = ∏ y, if y = i then P.prob i else (1 : ℚ) := by
    apply Finset.prod_congr rfl
    intro y _
    exact hsum y
  rw [hstep2]
  rw [Finset.prod_ite_eq' Finset.univ i (fun _ => P.prob i)]
  simp

/-- `Pr(¬f) = 1 - Pr(f)`: probability of a Boolean complement. In `BoolFunc X`,
`1 - f` is pointwise `f v && !(f v)`-style Boolean subtraction, which on the
constant-true `1` reduces to `Bool.not ∘ f`. The proof splits each summand by
`f v` and uses `sum_valProb_eq_one`. -/
theorem funcProb_sub_self_const_one (f : BoolFunc X) :
    P.funcProb (1 - f) = 1 - P.funcProb f := by
  unfold funcProb
  -- Rewrite each `(1 - f) v` to `!(f v)` and split the sum by cases on `f v`.
  have hsub : ∀ v : X → Bool, (1 - f : BoolFunc X) v = !(f v) := by
    intro v
    show ((1 : BoolFunc X) v && !(f v) : Bool) = !(f v)
    have h1 : (1 : BoolFunc X) v = true := rfl
    rw [h1]; simp
  have hstep :
      (∑ v : X → Bool, if ((1 - f : BoolFunc X) v : Bool) then P.valProb v else 0)
      = ∑ v : X → Bool, (P.valProb v - (if (f v : Bool) then P.valProb v else 0)) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [hsub v]
    by_cases hfv : f v = true
    · simp [hfv]
    · have hfv' : f v = false := by
        cases h : f v with
        | false => rfl
        | true => exact absurd h hfv
      simp [hfv']
  rw [hstep, Finset.sum_sub_distrib, P.sum_valProb_eq_one]

/-! ### Independence lemma

The independence lemma `funcProb_mul_disjoint` is the technical heart of the
read-once correctness theorem: `Pr(f * g) = Pr(f) * Pr(g)` whenever `f` and `g`
depend on disjoint variable supports. The proof splits each valuation
`v : X → Bool` into its restrictions on `S` and `Sᶜ` via
`Equiv.piEquivPiSubtypeProd`, factors the valuation probability over the
partition, and uses the marginalisation `∑_b (P̃_x b) = 1` to discard the
unused half on each of the two factors. -/

/-- **Independence lemma.** If `f`, `g : BoolFunc X` depend on disjoint
variable supports `S`, `T`, then `Pr(f * g) = Pr(f) * Pr(g)`.

The proof splits each valuation `v : X → Bool` into `(v|S, v|Sᶜ)` via
`Equiv.piEquivPiSubtypeProd`, factors `valProb v` as the product of the two
restricted products, and uses the marginalisations
`∑_{vS} (∏_{x ∈ S} P̃_x(vS x)) = 1` and
`∑_{vR} (∏_{x ∉ S} P̃_x(vR x)) = 1`
(both proved via `Fintype.prod_sum` and `sum_factor_at`) to collapse the
unused half on each side. -/
theorem funcProb_mul_disjoint {f g : BoolFunc X} {S T : Finset X}
    (hf : f.DependsOn S) (hg : g.DependsOn T) (hST : Disjoint S T) :
    P.funcProb (f * g) = P.funcProb f * P.funcProb g := by
  classical
  -- Per-variable factor.
  let h : X → Bool → ℚ := fun x b => if b then P.prob x else 1 - P.prob x
  -- Equivalence splitting valuations along S.
  let e : (X → Bool) ≃ ({x // x ∈ S} → Bool) × ({x // x ∉ S} → Bool) :=
    Equiv.piEquivPiSubtypeProd (fun x => x ∈ S) _
  -- Glue helper: stitch a Subtype-pair valuation back to a full one.
  let glue : ({x // x ∈ S} → Bool) → ({x // x ∉ S} → Bool) → (X → Bool) :=
    fun vS vR => e.symm (vS, vR)
  -- Default fillers (used to define `fS` and `gR`).
  let v0R : {x // x ∉ S} → Bool := fun _ => false
  let v0S : {x // x ∈ S} → Bool := fun _ => false
  -- "Restricted" Boolean functions on each half.
  let fS : ({x // x ∈ S} → Bool) → Bool := fun vS => f (glue vS v0R)
  let gR : ({x // x ∉ S} → Bool) → Bool := fun vR => g (glue v0S vR)
  -- Per-side probability products.
  let pS : ({x // x ∈ S} → Bool) → ℚ := fun vS => ∏ x : {x // x ∈ S}, h ↑x (vS x)
  let pR : ({x // x ∉ S} → Bool) → ℚ := fun vR => ∏ x : {x // x ∉ S}, h ↑x (vR x)
  -- Glue evaluates to vS on S and vR on Sᶜ.
  have hglue_in : ∀ vS vR (x : X) (hx : x ∈ S), glue vS vR x = vS ⟨x, hx⟩ := by
    intro vS vR x hx
    show (e.symm (vS, vR)) x = vS ⟨x, hx⟩
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  have hglue_out : ∀ vS vR (x : X) (hx : x ∉ S), glue vS vR x = vR ⟨x, hx⟩ := by
    intro vS vR x hx
    show (e.symm (vS, vR)) x = vR ⟨x, hx⟩
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  -- f depends only on the S-half of the valuation.
  have hfeq : ∀ vS vR, f (glue vS vR) = fS vS := fun vS vR =>
    hf _ _ fun x hxS => by rw [hglue_in _ _ _ hxS, hglue_in _ _ _ hxS]
  -- g depends only on the Sᶜ-half of the valuation (since T ⊆ Sᶜ).
  have hgeq : ∀ vS vR, g (glue vS vR) = gR vR := fun vS vR =>
    hg _ _ fun x hxT => by
      have hxnS : x ∉ S := Finset.disjoint_right.mp hST hxT
      rw [hglue_out _ _ _ hxnS, hglue_out _ _ _ hxnS]
  -- Valuation probability factors along the partition.
  have hval_split : ∀ vS vR, P.valProb (glue vS vR) = pS vS * pR vR := by
    intro vS vR
    show (∏ x, h x ((glue vS vR) x))
          = (∏ x : {x // x ∈ S}, h ↑x (vS x)) * (∏ x : {x // x ∉ S}, h ↑x (vR x))
    rw [← Finset.prod_mul_prod_compl S (fun x => h x ((glue vS vR) x))]
    congr 1
    · rw [Finset.prod_subtype (s := S) (p := fun x => x ∈ S) (fun _ => Iff.rfl)]
      refine Finset.prod_congr rfl ?_
      rintro ⟨x, hx⟩ _
      rw [hglue_in _ _ _ hx]
    · rw [Finset.prod_subtype (s := Sᶜ) (p := fun x => x ∉ S)
            (fun _ => by simp)]
      refine Finset.prod_congr rfl ?_
      rintro ⟨x, hx⟩ _
      rw [hglue_out _ _ _ hx]
  -- Per-variable column sum: `∑_b h x b = P.prob x + (1 - P.prob x) = 1`.
  have hsumcol : ∀ x, (∑ b : Bool, h x b) = 1 := by
    intro x
    show (∑ b : Bool, if b then P.prob x else 1 - P.prob x) = 1
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [hu, Finset.sum_insert (by decide : (false : Bool) ∉ ({true} : Finset Bool)),
        Finset.sum_singleton]
    simp
  -- Marginal sums on each half.
  have sum_pS_eq_one : (∑ vS : {x // x ∈ S} → Bool, pS vS) = 1 := by
    show (∑ vS : {x // x ∈ S} → Bool, ∏ x : {x // x ∈ S}, h ↑x (vS x)) = 1
    rw [← Fintype.prod_sum (fun (x : {x // x ∈ S}) (b : Bool) => h ↑x b)]
    exact Finset.prod_eq_one (fun x _ => hsumcol ↑x)
  have sum_pR_eq_one : (∑ vR : {x // x ∉ S} → Bool, pR vR) = 1 := by
    show (∑ vR : {x // x ∉ S} → Bool, ∏ x : {x // x ∉ S}, h ↑x (vR x)) = 1
    rw [← Fintype.prod_sum (fun (x : {x // x ∉ S}) (b : Bool) => h ↑x b)]
    exact Finset.prod_eq_one (fun x _ => hsumcol ↑x)
  -- Sum-of-valuations rewriting along the split.
  have hsum_iterated : ∀ F : (X → Bool) → ℚ,
      (∑ v : X → Bool, F v)
        = ∑ vS : {x // x ∈ S} → Bool, ∑ vR : {x // x ∉ S} → Bool, F (glue vS vR) := by
    intro F
    have h1 : (∑ v : X → Bool, F v)
        = ∑ p : ({x // x ∈ S} → Bool) × ({x // x ∉ S} → Bool), F (e.symm p) :=
      (Equiv.sum_comp e.symm F).symm
    rw [h1]
    exact Fintype.sum_prod_type' (fun vS vR => F (glue vS vR))
  -- Pr(f) = ∑_vS (if fS vS then pS vS else 0).
  have hPr_f : P.funcProb f = ∑ vS : {x // x ∈ S} → Bool,
                                (if fS vS then pS vS else 0) := by
    show (∑ v : X → Bool, if f v then P.valProb v else 0)
        = ∑ vS : {x // x ∈ S} → Bool, (if fS vS then pS vS else 0)
    rw [hsum_iterated (fun v => if f v then P.valProb v else 0)]
    refine Finset.sum_congr rfl ?_
    intro vS _
    simp_rw [hfeq vS, hval_split vS]
    by_cases hfs : fS vS
    · simp_rw [if_pos hfs]
      rw [← Finset.mul_sum, sum_pR_eq_one, mul_one]
    · simp_rw [if_neg hfs]; simp
  -- Pr(g) = ∑_vR (if gR vR then pR vR else 0).
  have hPr_g : P.funcProb g = ∑ vR : {x // x ∉ S} → Bool,
                                (if gR vR then pR vR else 0) := by
    show (∑ v : X → Bool, if g v then P.valProb v else 0)
        = ∑ vR : {x // x ∉ S} → Bool, (if gR vR then pR vR else 0)
    rw [hsum_iterated (fun v => if g v then P.valProb v else 0)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro vR _
    simp_rw [hgeq _ vR, hval_split _ vR]
    by_cases hgs : gR vR
    · simp_rw [if_pos hgs]
      rw [← Finset.sum_mul, sum_pS_eq_one, one_mul]
    · simp_rw [if_neg hgs]; simp
  -- Pr(f * g) factors via Fintype.sum_mul_sum.
  show (∑ v : X → Bool, if ((f * g) v : Bool) then P.valProb v else 0)
      = P.funcProb f * P.funcProb g
  rw [hsum_iterated (fun v => if ((f * g) v : Bool) then P.valProb v else 0)]
  rw [hPr_f, hPr_g, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro vS _
  refine Finset.sum_congr rfl ?_
  intro vR _
  have hcomb : ((f * g) (glue vS vR) : Bool) = (fS vS && gR vR) := by
    show (f (glue vS vR) && g (glue vS vR)) = (fS vS && gR vR)
    rw [hfeq, hgeq]
  rw [hcomb, hval_split]
  cases hf' : fS vS <;> cases hg' : gR vR <;> simp

/-- `Pr(f + g) = Pr(f) + Pr(g) - Pr(f * g)`: the universal inclusion-exclusion
identity for the BoolFunc disjunction (`+`) and conjunction (`*`). No
disjointness hypothesis is needed; the formula holds pointwise on each summand
via the Bool identity `(b₁ || b₂).toℚ = b₁.toℚ + b₂.toℚ - (b₁ && b₂).toℚ`. -/
theorem funcProb_add_eq (f g : BoolFunc X) :
    P.funcProb (f + g) = P.funcProb f + P.funcProb g - P.funcProb (f * g) := by
  unfold funcProb
  -- The Bool identity, lifted to the ℚ-weighted sum.
  have hpoint : ∀ v : X → Bool,
      (if ((f + g : BoolFunc X) v : Bool) then P.valProb v else 0)
      = (if (f v : Bool) then P.valProb v else 0)
        + (if (g v : Bool) then P.valProb v else 0)
        - (if ((f * g : BoolFunc X) v : Bool) then P.valProb v else 0) := by
    intro v
    show (if (f v || g v : Bool) then P.valProb v else 0)
        = (if (f v : Bool) then P.valProb v else 0)
          + (if (g v : Bool) then P.valProb v else 0)
          - (if ((f v && g v : Bool)) then P.valProb v else 0)
    cases hfv : f v <;> cases hgv : g v <;> simp
  rw [show (∑ v : X → Bool, if ((f + g : BoolFunc X) v : Bool) then P.valProb v else 0)
        = ∑ v : X → Bool,
            ((if (f v : Bool) then P.valProb v else 0)
            + (if (g v : Bool) then P.valProb v else 0)
            - (if ((f * g : BoolFunc X) v : Bool) then P.valProb v else 0)) from
    Finset.sum_congr rfl (fun v _ => hpoint v)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

end ProbAssignment
