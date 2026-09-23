import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Polynomial
import Surreal.Algebra.TailSpan

/-!
# Analytic square classes, the exponential graph and hereditary jet spans

This file proves `tail:lem:analyticclasses`, `tail:lem:expgraph` and `tail:lem:jetspan` in
`docs/surreal/tail-spans-and-differential-transcendence/article.tex`. The first and third are
the analytic inputs of `tail:thm:mixed`, about the functions `a_n(z) = 1 - z / 2^n` and the
jet vectors `v_n`; `tail:lem:expgraph` enters only through the proof of `tail:lem:jetspan`. The
companion results `tail:lem:stabilization` and `tail:lem:multilinear` are in
`Surreal.Algebra.TailSpan`.

* `tail:lem:analyticclasses`. Over any field `𝕜` and for pairwise distinct nonzero `β_i`,
  a finite product `∏ (1 - z / β_i) ^ e_i` is a square in `𝕜(z)` exactly when every `e_i`
  is even (`isSquare_prod_linearClass_pow_iff`). As in the source, a polynomial that is a
  square in `𝕜(z)` has even multiplicity at every point: it is the square of a polynomial
  because `𝕜[z]` is integrally closed. The product has multiplicity `e_i` at `β_i`. For
  `a_n = 1 - z / 2^n` (`analyticClass`) the classes in `ℂ(z)^× / ℂ(z)^{×2}` are therefore
  independent, and no product over a nonempty finite `J` is a square
  (`not_isSquare_prod_analyticClass`). Every `n ∈ ℕ` is allowed, including `n = 0`.
* `tail:lem:expgraph`. For `b ∈ ℂ` with `‖b‖ > 1` and a nonzero `R ∈ ℂ[X][Y]`,
  `R(n, b^n) ≠ 0` for all large `n` (`eventually_evalEval_natCast_pow_ne_zero`). The proof
  follows the source: the leading term `p_M(n) b^{Mn}` dominates, because `p_M(n)` stays
  away from zero and the other coefficients grow polynomially. The source's case `b = 2`
  is `finite_setOf_evalEval_two_pow_eq_zero` for `ℂ[X][X]`, whose inner variable is `X`
  and outer variable is `Y`. `finite_setOf_mvEval_two_pow_eq_zero` states it for
  `MvPolynomial (Fin 2) ℂ`. Both give finiteness over all `n ∈ ℕ`, so in particular over
  the positive integers.
* `tail:lem:jetspan`. The algebraic core `span_jetVector_eq_top` holds over any field. If
  no single nonzero `R(X, Y)` vanishes at all the points `(γ_n, β_n)`, `n ∈ A`, and
  `c_j ≠ 0` for `j ≤ J`, then the vectors `(c_j γ_n^k / (z - β_n)^j)_{j ≤ J, k ≤ K}`
  span `𝕜(z)^{(J+1)(K+1)}`. The proof follows the source. The denominators of a nonzero
  annihilating functional are cleared to polynomials `C_{jk}`, not all zero. Multiplying
  by `(z - β_n)^{j_*}` for the top layer `j_*` and evaluating the polynomial identity at
  `β_n` gives `∑_k C_{j_* k}(β_n) γ_n^k = 0` for all `n ∈ A`, i.e. a nonzero `R` vanishing
  at all the points. With `β_n = b^n`, `γ_n = n` and `‖b‖ > 1`, the exponential-graph
  lemma supplies the hypothesis for every infinite `A` (`span_jetVector_pow_eq_top`). For
  `b = 2` and the falling factorials `c_j = (1/2)(1/2 - 1)⋯(1/2 - j + 1)` (`halfFalling`),
  every infinite subfamily of the source's `v_n` (`sourceJetVector`) spans
  (`span_sourceJetVector_eq_top`), and so does every cofinite part of it
  (`span_sourceJetVector_diff_eq_top`). The latter is also given in the form of the
  hypothesis of `TailSpan.multilinear_baseChange_eq_zero`
  (`span_sourceJetVector_compl_eq_top`) and as `TailSpan.cofiniteSpan = ⊤`
  (`cofiniteSpan_sourceJetVector_eq_top`).

Nothing in these three lemmas remains pending. The analytic setting in which the source uses
them is not formalized here: the square roots `h_n`, the two derivations, the jet formula
`tail:eq:hnjet`, and `tail:thm:mixed` itself.
-/

noncomputable section

namespace Surreal.TailAnalytic

open Polynomial Filter Topology Submodule

/-! ### Square classes of linear rational functions -/

section SquareClasses

variable {𝕜 : Type*} [Field 𝕜]

/-- A polynomial that becomes a square in the rational function field has even
multiplicity at every point. -/
theorem even_rootMultiplicity_of_isSquare {p : 𝕜[X]}
    (hp : IsSquare (algebraMap 𝕜[X] (RatFunc 𝕜) p)) (x : 𝕜) :
    Even (p.rootMultiplicity x) := by
  obtain ⟨r, hr⟩ := hp
  have hint : IsIntegral 𝕜[X] (r ^ 2) := by
    rw [sq, ← hr]
    exact isIntegral_algebraMap
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow two_pos hint
  rw [← map_mul] at hr
  obtain rfl : p = y * y := RatFunc.algebraMap_injective 𝕜 hr
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [rootMultiplicity_mul (mul_ne_zero hy hy)]
    exact ⟨_, rfl⟩

/-- The rational function `1 - z / β`. -/
def linearClass (β : 𝕜) : RatFunc 𝕜 :=
  1 - RatFunc.X / RatFunc.C β

theorem linearClass_eq (β : 𝕜) :
    linearClass β = algebraMap 𝕜[X] (RatFunc 𝕜) (1 - C β⁻¹ * X) := by
  rw [linearClass, map_sub, map_one, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_inv₀, div_eq_mul_inv, mul_comm]

theorem one_sub_C_inv_mul_X_eq {β : 𝕜} (hβ : β ≠ 0) :
    (1 - C β⁻¹ * X : 𝕜[X]) = C (-β⁻¹) * (X - C β) := by
  rw [mul_sub, ← C_mul, neg_mul, inv_mul_cancel₀ hβ, C_neg, C_neg, C_1]
  ring

theorem one_sub_C_inv_mul_X_ne_zero {β : 𝕜} (hβ : β ≠ 0) : (1 - C β⁻¹ * X : 𝕜[X]) ≠ 0 := by
  rw [one_sub_C_inv_mul_X_eq hβ]
  exact mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 (inv_ne_zero hβ))) (X_sub_C_ne_zero β)

theorem linearClass_ne_zero {β : 𝕜} (hβ : β ≠ 0) : linearClass β ≠ 0 := by
  rw [linearClass_eq]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective 𝕜)).2 (one_sub_C_inv_mul_X_ne_zero hβ)

theorem rootMultiplicity_one_sub_C_inv_mul_X_pow {β : 𝕜} (hβ : β ≠ 0) (e : ℕ) :
    ((1 - C β⁻¹ * X : 𝕜[X]) ^ e).rootMultiplicity β = e := by
  rw [one_sub_C_inv_mul_X_eq hβ, mul_pow, ← C_pow, rootMultiplicity_mul_X_sub_C_pow
    (C_ne_zero.2 (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hβ)))), rootMultiplicity_C,
    zero_add]

/-- Generic form of `tail:lem:analyticclasses`: for pairwise distinct nonzero points `β i`,
a finite product `∏ (1 - z / β i) ^ e i` is a square in `𝕜(z)` exactly when every exponent
is even. Equivalently, the square classes of the `1 - z / β i` are independent over `𝔽₂`. -/
theorem isSquare_prod_linearClass_pow_iff {I : Type*} {β : I → 𝕜} (hβ : Function.Injective β)
    (hβ0 : ∀ i, β i ≠ 0) (s : Finset I) (e : I → ℕ) :
    IsSquare (∏ i ∈ s, linearClass (β i) ^ e i) ↔ ∀ i ∈ s, Even (e i) := by
  classical
  constructor
  · intro h i hi
    have hprod : ∏ i ∈ s, linearClass (β i) ^ e i =
        algebraMap 𝕜[X] (RatFunc 𝕜) (∏ i ∈ s, (1 - C (β i)⁻¹ * X) ^ e i) := by
      rw [map_prod]
      simp only [map_pow, linearClass_eq]
    rw [hprod] at h
    have hev := even_rootMultiplicity_of_isSquare h (β i)
    have hrest : ¬ IsRoot (∏ j ∈ s.erase i, (1 - C (β j)⁻¹ * X) ^ e j) (β i) := by
      rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff]
      rintro ⟨j, hj, hzero⟩
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X] at hzero
      have h1 : (β j)⁻¹ * β i = 1 := by
        linear_combination -(eq_zero_of_pow_eq_zero hzero)
      exact hji (hβ ((inv_mul_eq_one₀ (hβ0 j)).1 h1))
    have hne : (1 - C (β i)⁻¹ * X) ^ e i * ∏ j ∈ s.erase i, (1 - C (β j)⁻¹ * X) ^ e j ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (one_sub_C_inv_mul_X_ne_zero (hβ0 i)))
        (Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (one_sub_C_inv_mul_X_ne_zero (hβ0 j)))
    rw [← Finset.mul_prod_erase s _ hi, rootMultiplicity_mul hne,
      rootMultiplicity_one_sub_C_inv_mul_X_pow (hβ0 i), rootMultiplicity_eq_zero hrest,
      add_zero] at hev
    exact hev
  · intro h
    exact Finset.isSquare_prod _ fun i hi => (h i hi).isSquare_pow _

/-- Generic form of `tail:lem:analyticclasses`: no nonempty finite product of the
`1 - z / β i` is a square in `𝕜(z)`. -/
theorem not_isSquare_prod_linearClass {I : Type*} {β : I → 𝕜} (hβ : Function.Injective β)
    (hβ0 : ∀ i, β i ≠ 0) {s : Finset I} (hs : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, linearClass (β i)) := by
  have h := isSquare_prod_linearClass_pow_iff hβ hβ0 s fun _ => 1
  simp only [pow_one] at h
  rw [h]
  obtain ⟨i, hi⟩ := hs
  exact fun h' => Nat.not_even_one (h' i hi)

end SquareClasses

/-- The source's functions `a_n(z) = 1 - z / 2^n` (the radicands of `h_n`) in `M = ℂ(z)`,
defined here for every `n ∈ ℕ`. -/
def analyticClass (n : ℕ) : RatFunc ℂ :=
  linearClass ((2 : ℂ) ^ n)

theorem two_pow_injective : Function.Injective fun n : ℕ => (2 : ℂ) ^ n := by
  intro m n h
  have h' : ((2 ^ m : ℕ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := by
    push_cast
    exact h
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective h')

theorem two_pow_ne_zero (n : ℕ) : (2 : ℂ) ^ n ≠ 0 :=
  pow_ne_zero _ two_ne_zero

/-- Each `a_n = 1 - z / 2^n` is nonzero, hence a unit of the field `ℂ(z)`. -/
theorem analyticClass_ne_zero (n : ℕ) : analyticClass n ≠ 0 :=
  linearClass_ne_zero (two_pow_ne_zero n)

/-- `tail:lem:analyticclasses`, exponent form: `∏_{n ∈ s} a_n ^ e_n` is a square in `ℂ(z)`
exactly when every exponent is even, so the classes of the `a_n` in
`ℂ(z)^× / ℂ(z)^{×2}` are independent. -/
theorem isSquare_prod_analyticClass_pow_iff (s : Finset ℕ) (e : ℕ → ℕ) :
    IsSquare (∏ n ∈ s, analyticClass n ^ e n) ↔ ∀ n ∈ s, Even (e n) :=
  isSquare_prod_linearClass_pow_iff two_pow_injective two_pow_ne_zero s e

/-- `tail:lem:analyticclasses`: for every nonempty finite `J`, the product
`∏_{n ∈ J} (1 - z / 2^n)` is not a square in `ℂ(z)`. -/
theorem not_isSquare_prod_analyticClass {s : Finset ℕ} (hs : s.Nonempty) :
    ¬ IsSquare (∏ n ∈ s, analyticClass n) :=
  not_isSquare_prod_linearClass two_pow_injective two_pow_ne_zero hs

/-! ### The exponential graph -/

section ExpGraph

/-- Evaluation of a bivariate polynomial as a sum over the powers of the outer variable. -/
theorem evalEval_eq_sum_range {S : Type*} [CommSemiring S] (R : S[X][X]) (x y : S) :
    R.evalEval x y = ∑ m ∈ Finset.range (R.natDegree + 1), (R.coeff m).eval x * y ^ m := by
  rw [evalEval, eval_eq_sum_range (p := R) (C y), eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_C]

/-- Polynomial growth: away from the unit disk a polynomial of degree at most `N` is
bounded by its coefficient norm times `‖x‖ ^ N`. -/
theorem norm_eval_le_of_one_le {q : ℂ[X]} {N : ℕ} (hq : q.natDegree ≤ N) {x : ℂ}
    (hx : 1 ≤ ‖x‖) :
    ‖q.eval x‖ ≤ (∑ i ∈ Finset.range (N + 1), ‖q.coeff i‖) * ‖x‖ ^ N := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hx (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) (norm_nonneg _)

/-- `tail:lem:expgraph`, asymptotic form, for any base `b` with `‖b‖ > 1`: a nonzero
`R(X, Y)` satisfies `R(n, b^n) ≠ 0` for all sufficiently large `n`. Here `X` is the inner
and `Y` the outer variable of `ℂ[X][X]`. -/
theorem eventually_evalEval_natCast_pow_ne_zero {b : ℂ} (hb : 1 < ‖b‖) {R : ℂ[X][X]}
    (hR : R ≠ 0) : ∀ᶠ n : ℕ in atTop, R.evalEval (n : ℂ) (b ^ n) ≠ 0 := by
  have hP : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hR
  -- The leading coefficient `p_M(n)` stays away from zero.
  obtain ⟨c₀, hc₀, hlow⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ᶠ n : ℕ in atTop, c₀ ≤ ‖R.leadingCoeff.eval (n : ℂ)‖ := by
    by_cases hd : 0 < R.leadingCoeff.degree
    · refine ⟨1, one_pos, ?_⟩
      have ht := R.leadingCoeff.tendsto_norm_atTop hd (l := atTop)
        (z := fun n : ℕ => (n : ℂ)) (by simpa using tendsto_natCast_atTop_atTop)
      exact ht.eventually_ge_atTop 1
    · have hc : R.leadingCoeff = C (R.leadingCoeff.coeff 0) :=
        eq_C_of_degree_le_zero (not_lt.1 hd)
      have h0 : R.leadingCoeff.coeff 0 ≠ 0 := fun h => hP (by rw [hc, h, C_0])
      refine ⟨‖R.leadingCoeff.coeff 0‖, norm_pos_iff.2 h0, Eventually.of_forall fun n => ?_⟩
      exact le_of_eq (by rw [hc]; simp)
  -- The lower coefficients grow at most polynomially.
  set M := R.natDegree
  set N := ∑ m ∈ Finset.range M, (R.coeff m).natDegree
  set B := ∑ m ∈ Finset.range M, ∑ i ∈ Finset.range (N + 1), ‖(R.coeff m).coeff i‖
  have hgrowth : ∀ m ∈ Finset.range M, ∀ x : ℂ, 1 ≤ ‖x‖ →
      ‖(R.coeff m).eval x‖ ≤ B * ‖x‖ ^ N := by
    intro m hm x hx
    refine (norm_eval_le_of_one_le
      (Finset.single_le_sum (f := fun m => (R.coeff m).natDegree)
        (fun _ _ => Nat.zero_le _) hm) hx).trans ?_
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun m => ∑ i ∈ Finset.range (N + 1), ‖(R.coeff m).coeff i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hm)
      (pow_nonneg (norm_nonneg _) _)
  -- The exponential beats the polynomial growth.
  have hb0 : 0 < ‖b‖ := one_pos.trans hb
  have hdecay : ∀ᶠ n : ℕ in atTop, (M * B) * (n : ℝ) ^ N < c₀ * ‖b‖ ^ n := by
    have ht : Tendsto (fun n : ℕ => (M * B) * ((n : ℝ) ^ N / ‖b‖ ^ n)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_const_div_const_pow_of_one_lt N hb).const_mul ((M : ℝ) * B)
    filter_upwards [ht.eventually_lt_const hc₀] with n hn
    rwa [mul_div_assoc', div_lt_iff₀ (pow_pos hb0 n)] at hn
  filter_upwards [hlow, hdecay, eventually_ge_atTop 1] with n hn1 hn2 hn3 hzero
  have hx : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by simpa using (Nat.one_le_cast.2 hn3 : (1 : ℝ) ≤ n)
  rw [evalEval_eq_sum_range, Finset.sum_range_succ] at hzero
  set L := ∑ m ∈ Finset.range M, (R.coeff m).eval (n : ℂ) * (b ^ n) ^ m
  have hlead : ‖R.leadingCoeff.eval (n : ℂ) * (b ^ n) ^ M‖ = ‖L‖ := by
    rw [← norm_neg L, ← eq_neg_of_add_eq_zero_right hzero]
    rfl
  have hrn : 1 ≤ ‖b‖ ^ n := one_le_pow₀ hb.le
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · have hL : L = 0 := by simp [L, hM0]
    rw [hL, norm_zero, norm_mul, norm_pow, hM0, pow_zero, mul_one] at hlead
    linarith
  · have hLle : ‖L‖ ≤ M * (B * (n : ℝ) ^ N * (‖b‖ ^ n) ^ (M - 1)) := by
      refine (norm_sum_le (Finset.range M)
        fun m => (R.coeff m).eval (n : ℂ) * (b ^ n) ^ m).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => B * (n : ℝ) ^ N * (‖b‖ ^ n) ^ (M - 1))
        fun m hm => ?_).trans (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul])
      rw [norm_mul, norm_pow, norm_pow]
      have h1 := hgrowth m hm _ hx
      rw [Complex.norm_natCast] at h1
      have h2 : (‖b‖ ^ n) ^ m ≤ (‖b‖ ^ n) ^ (M - 1) :=
        pow_le_pow_right₀ hrn (Nat.le_sub_one_of_lt (Finset.mem_range.1 hm))
      exact mul_le_mul h1 h2 (pow_nonneg (by positivity) _)
        (mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (by positivity))
    have hpowpos : 0 < (‖b‖ ^ n) ^ (M - 1) := pow_pos (pow_pos hb0 n) _
    have hlt : (M : ℝ) * (B * (n : ℝ) ^ N * (‖b‖ ^ n) ^ (M - 1)) <
        ‖R.leadingCoeff.eval (n : ℂ)‖ * (‖b‖ ^ n) ^ M := by
      calc (M : ℝ) * (B * (n : ℝ) ^ N * (‖b‖ ^ n) ^ (M - 1))
          = ((M : ℝ) * B * (n : ℝ) ^ N) * (‖b‖ ^ n) ^ (M - 1) := by ring
        _ < (c₀ * ‖b‖ ^ n) * (‖b‖ ^ n) ^ (M - 1) := mul_lt_mul_of_pos_right hn2 hpowpos
        _ = c₀ * (‖b‖ ^ n) ^ M := by
          rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hMpos]
        _ ≤ ‖R.leadingCoeff.eval (n : ℂ)‖ * (‖b‖ ^ n) ^ M :=
          mul_le_mul_of_nonneg_right hn1 (by positivity)
    rw [norm_mul, norm_pow, norm_pow] at hlead
    linarith

/-- `tail:lem:expgraph` for any base `b` with `‖b‖ > 1`: a nonzero `R(X, Y)` vanishes at
`(n, b^n)` for only finitely many natural numbers `n`. -/
theorem finite_setOf_evalEval_natCast_pow_eq_zero {b : ℂ} (hb : 1 < ‖b‖) {R : ℂ[X][X]}
    (hR : R ≠ 0) : {n : ℕ | R.evalEval (n : ℂ) (b ^ n) = 0}.Finite := by
  have h := eventually_evalEval_natCast_pow_ne_zero hb hR
  rw [← Nat.cofinite_eq_atTop] at h
  simpa using Filter.eventually_cofinite.1 h

/-- `tail:lem:expgraph`: if `R(X, Y) ∈ ℂ[X, Y]` is nonzero, then `R(n, 2^n) = 0` for only
finitely many natural numbers `n`, in particular for only finitely many positive
integers. The inner variable of `ℂ[X][X]` is `X` and the outer one is `Y`. -/
theorem finite_setOf_evalEval_two_pow_eq_zero {R : ℂ[X][X]} (hR : R ≠ 0) :
    {n : ℕ | R.evalEval (n : ℂ) ((2 : ℂ) ^ n) = 0}.Finite :=
  finite_setOf_evalEval_natCast_pow_eq_zero (by simp) hR

/-- Evaluation is compatible with `Bivariate.equivMvPolynomial : S[X][X] ≃ S[X, Y]`. -/
theorem mvEval_equivMvPolynomial {S : Type*} [CommSemiring S] (x y : S) (p : S[X][X]) :
    MvPolynomial.eval ![x, y] (Bivariate.equivMvPolynomial S p) = p.evalEval x y := by
  have h : (MvPolynomial.aeval ![x, y]).comp (Bivariate.equivMvPolynomial S).toAlgHom =
      aevalAeval x y := by
    apply algHom_ext'
    · ext
      simp
    · simp
  have hp : ((MvPolynomial.aeval ![x, y]).comp (Bivariate.equivMvPolynomial S).toAlgHom) p =
      aevalAeval x y p := by
    rw [h]
  rw [coe_aevalAeval_eq_evalEval] at hp
  rw [← hp]
  rfl

/-- `tail:lem:expgraph` with `R ∈ ℂ[X, Y]` written as a polynomial in two named variables:
if `R ≠ 0`, then `R(n, 2^n) = 0` for only finitely many natural numbers `n`. -/
theorem finite_setOf_mvEval_two_pow_eq_zero {R : MvPolynomial (Fin 2) ℂ} (hR : R ≠ 0) :
    {n : ℕ | MvPolynomial.eval ![(n : ℂ), (2 : ℂ) ^ n] R = 0}.Finite := by
  set p := (Bivariate.equivMvPolynomial ℂ).symm R
  have hp : p ≠ 0 := fun h => hR (by
    rw [← (Bivariate.equivMvPolynomial ℂ).apply_symm_apply R]
    change Bivariate.equivMvPolynomial ℂ p = 0
    rw [h, map_zero])
  have hR' : R = Bivariate.equivMvPolynomial ℂ p := by simp [p]
  simpa only [hR', mvEval_equivMvPolynomial] using finite_setOf_evalEval_two_pow_eq_zero hp

end ExpGraph

/-! ### Hereditary full jet span -/

section JetSpan

variable {𝕜 : Type*} [Field 𝕜]

/-- The jet coefficient vector `(c_j γ^k / (z - β)^j)_{0 ≤ j ≤ J, 0 ≤ k ≤ K}` in
`𝕜(z)^{(J+1)(K+1)}`. -/
def jetVector (c : ℕ → 𝕜) (J K : ℕ) (β γ : 𝕜) : Fin (J + 1) × Fin (K + 1) → RatFunc 𝕜 :=
  fun jk => RatFunc.C (c jk.1 * γ ^ (jk.2 : ℕ)) / (RatFunc.X - RatFunc.C β) ^ (jk.1 : ℕ)

theorem ratFunc_X_sub_C_ne_zero (β : 𝕜) : (RatFunc.X - RatFunc.C β : RatFunc 𝕜) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective 𝕜)).2 (X_sub_C_ne_zero β)

/-- Clearing the pole at `β`: if `∑ D_i w_i / (z - β)^{e_i} = 0` with polynomial `D_i` and
`D_i = 0` whenever `e_i > m`, then multiplying by `(z - β)^m` and evaluating the resulting
polynomial identity at `β` leaves only the layer `e_i = m`. -/
theorem sum_eval_mul_zero_pow_eq_zero {ι : Type*} [Fintype ι] (D : ι → 𝕜[X]) (e : ι → ℕ)
    (w : ι → 𝕜) (β : 𝕜) (m : ℕ) (hD : ∀ i, m < e i → D i = 0)
    (h : ∑ i, algebraMap 𝕜[X] (RatFunc 𝕜) (D i) * RatFunc.C (w i) /
      (RatFunc.X - RatFunc.C β) ^ e i = 0) :
    ∑ i, (D i).eval β * w i * 0 ^ (m - e i) = 0 := by
  have hQ : algebraMap 𝕜[X] (RatFunc 𝕜) (∑ i, D i * C (w i) * (X - C β) ^ (m - e i)) =
      (RatFunc.X - RatFunc.C β) ^ m * ∑ i, algebraMap 𝕜[X] (RatFunc 𝕜) (D i) *
        RatFunc.C (w i) / (RatFunc.X - RatFunc.C β) ^ e i := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : m < e i
    · simp [hD i hi]
    · rw [map_mul, map_mul, map_pow, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
        RatFunc.algebraMap_C, ← pow_sub_mul_pow _ (not_lt.1 hi),
        mul_assoc ((RatFunc.X - RatFunc.C β) ^ (m - e i)),
        mul_div_cancel₀ _ (pow_ne_zero _ (ratFunc_X_sub_C_ne_zero β))]
      ring
  rw [h, mul_zero] at hQ
  have hQ0 := RatFunc.algebraMap_injective 𝕜 (hQ.trans (map_zero _).symm)
  have := congrArg (eval β) hQ0
  simpa [eval_finsetSum] using this

/-- Generic form of `tail:lem:jetspan`. Let `c_j ≠ 0` for `j ≤ J`, and let `(γ_n, β_n)`,
`n ∈ A`, be points not all on the zero set of any nonzero `R(X, Y)`, i.e. for each nonzero
`R` some `n ∈ A` has `R(γ_n, β_n) ≠ 0`. Then the jet vectors `(c_j γ_n^k / (z - β_n)^j)`,
`n ∈ A`, span `𝕜(z)^{(J+1)(K+1)}`. -/
theorem span_jetVector_eq_top {I : Type*} (c : ℕ → 𝕜) {J : ℕ} (hc : ∀ j ≤ J, c j ≠ 0)
    (K : ℕ) (β γ : I → 𝕜) {A : Set I}
    (hA : ∀ R : 𝕜[X][X], R ≠ 0 → ∃ n ∈ A, R.evalEval (γ n) (β n) ≠ 0) :
    span (RatFunc 𝕜) ((fun n => jetVector c J K (β n) (γ n)) '' A) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hspan) inferInstance
  -- The functional kills every vector of the family.
  have hfv : ∀ n ∈ A, f (jetVector c J K (β n) (γ n)) = 0 := by
    intro n hn
    have hmem := Submodule.mem_map_of_mem (f := f)
      (subset_span ⟨n, hn, rfl⟩ : jetVector c J K (β n) (γ n) ∈
        span (RatFunc 𝕜) ((fun n => jetVector c J K (β n) (γ n)) '' A))
    rw [hf] at hmem
    exact (Submodule.mem_bot _).1 hmem
  -- Its coefficients.
  set a : Fin (J + 1) × Fin (K + 1) → RatFunc 𝕜 :=
    fun i => f fun j => if i = j then 1 else 0
  have hfa : ∀ x, f x = ∑ i, x i * a i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    rfl
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext fun x => by rw [hfa]; simp [h])
  -- Clear the denominators of the coefficients.
  obtain ⟨⟨b, hb⟩, hbint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝕜[X]) (S := RatFunc 𝕜) a
  have hex : ∀ i, ∃ P : 𝕜[X],
      algebraMap 𝕜[X] (RatFunc 𝕜) P = algebraMap 𝕜[X] (RatFunc 𝕜) b * a i := by
    intro i
    obtain ⟨P, hP⟩ := hbint i
    exact ⟨P, by rw [hP, Algebra.smul_def]⟩
  choose P hP using hex
  have hb0 : algebraMap 𝕜[X] (RatFunc 𝕜) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  set D : Fin (J + 1) × Fin (K + 1) → 𝕜[X] := fun i => C (c i.1) * P i
  have hD₀ : D i₀ ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.2 (hc _ (Nat.lt_succ_iff.1 i₀.1.2))) fun h => ?_
    have h' := hP i₀
    rw [h, map_zero] at h'
    exact mul_ne_zero hb0 hi₀ h'.symm
  -- The cleared relation `∑ D_{jk} γ_n^k / (z - β_n)^j = 0`.
  have hrel : ∀ n ∈ A, ∑ i, algebraMap 𝕜[X] (RatFunc 𝕜) (D i) * RatFunc.C (γ n ^ (i.2 : ℕ)) /
      (RatFunc.X - RatFunc.C (β n)) ^ (i.1 : ℕ) = 0 := by
    intro n hn
    have h0 := hfv n hn
    rw [hfa] at h0
    calc _ = algebraMap 𝕜[X] (RatFunc 𝕜) b * ∑ i, jetVector c J K (β n) (γ n) i * a i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [D, map_mul, RatFunc.algebraMap_C, hP, jetVector]
          ring
      _ = 0 := by rw [h0, mul_zero]
  -- The top layer `j_*`.
  set S := Finset.univ.filter fun j : Fin (J + 1) => ∃ k, D (j, k) ≠ 0
  have hS : S.Nonempty := ⟨i₀.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, i₀.2, hD₀⟩⟩
  set js := S.max' hS
  obtain ⟨k₀, hk₀⟩ : ∃ k, D (js, k) ≠ 0 := (Finset.mem_filter.1 (S.max'_mem hS)).2
  have htop : ∀ i : Fin (J + 1) × Fin (K + 1), (js : ℕ) < i.1 → D i = 0 := by
    intro i hi
    by_contra hne
    have hmem : i.1 ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, i.2, hne⟩
    have hle : (i.1 : ℕ) ≤ js := Fin.le_def.1 (S.le_max' _ hmem)
    omega
  -- The polynomial `R'(X, Y) = ∑_k D_{j_* k}(X) Y^k` and its swap `R(X, Y) = R'(Y, X)`.
  set R' : 𝕜[X][X] := ∑ k : Fin (K + 1), C (D (js, k)) * X ^ (k : ℕ)
  have hR'eval : ∀ x y : 𝕜,
      R'.evalEval x y = ∑ k : Fin (K + 1), (D (js, k)).eval x * y ^ (k : ℕ) := by
    intro x y
    simp only [R', evalEval_finsetSum, evalEval_mul, evalEval_C, evalEval_pow, evalEval_X]
  have hR'coeff : R'.coeff (k₀ : ℕ) = D (js, k₀) := by
    simp only [R', finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single k₀]
    · simp
    · intro k _ hk
      rw [if_neg]
      exact fun h => hk (Fin.ext h.symm)
    · simp
  have hR' : R' ≠ 0 := fun h => hk₀ (by rw [← hR'coeff, h, coeff_zero])
  have hR : Bivariate.swap R' ≠ 0 := fun h =>
    hR' (by rw [← Bivariate.swap_swap_apply R', h, map_zero])
  obtain ⟨n, hn, hne⟩ := hA _ hR
  apply hne
  have hswap := Bivariate.aevalAeval_swap (R := 𝕜) (γ n) (β n) R'
  rw [coe_aevalAeval_eq_evalEval, coe_aevalAeval_eq_evalEval] at hswap
  rw [hswap, hR'eval]
  have hlayer := sum_eval_mul_zero_pow_eq_zero D (fun i => (i.1 : ℕ))
    (fun i => γ n ^ (i.2 : ℕ)) (β n) js htop (hrel n hn)
  refine Eq.trans ?_ hlayer
  rw [Fintype.sum_prod_type, Finset.sum_eq_single js]
  · simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [zero_pow (Nat.sub_ne_zero_of_lt (Fin.lt_def.1 hlt)), mul_zero]
    · rw [htop (j, k) (Fin.lt_def.1 hgt), eval_zero, zero_mul, zero_mul]
  · simp

end JetSpan

/-! ### The source jet vectors -/

/-- The falling factorial `c_j = (1/2)(1/2 - 1)⋯(1/2 - j + 1)`, with `c_0 = 1`. -/
def halfFalling (j : ℕ) : ℂ :=
  ∏ i ∈ Finset.range j, ((1 : ℂ) / 2 - i)

theorem halfFalling_zero : halfFalling 0 = 1 := by
  simp [halfFalling]

theorem halfFalling_succ (j : ℕ) : halfFalling (j + 1) = halfFalling j * (1 / 2 - j) :=
  Finset.prod_range_succ _ _

/-- Every `c_j` is nonzero. -/
theorem halfFalling_ne_zero (j : ℕ) : halfFalling j ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ h => ?_
  have h2 : ((2 * i : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
    push_cast
    linear_combination -2 * h
  have h3 := Nat.cast_injective h2
  omega

/-- The source's jet vector `v_n = (c_j n^k / (z - 2^n)^j)_{0 ≤ j ≤ J, 0 ≤ k ≤ K}` in
`M^{(J+1)(K+1)}`, `M = ℂ(z)`. -/
def sourceJetVector (J K n : ℕ) : Fin (J + 1) × Fin (K + 1) → RatFunc ℂ :=
  jetVector halfFalling J K ((2 : ℂ) ^ n) (n : ℂ)

/-- `tail:lem:jetspan` for arbitrary constants `c_j ≠ 0` and any base `‖b‖ > 1`, along an
injective reindexing `ι`: for every infinite index set `T`, the vectors
`(c_j ι(t)^k / (z - b^{ι(t)})^j)`, `t ∈ T`, span the whole space. -/
theorem span_jetVector_pow_eq_top (c : ℕ → ℂ) {J : ℕ} (hc : ∀ j ≤ J, c j ≠ 0) (K : ℕ)
    {b : ℂ} (hb : 1 < ‖b‖) {I : Type*} {ι : I → ℕ} (hι : Function.Injective ι) {T : Set I}
    (hT : T.Infinite) :
    span (RatFunc ℂ) ((fun t => jetVector c J K (b ^ ι t) (ι t : ℂ)) '' T) = ⊤ :=
  span_jetVector_eq_top c hc K (fun t => b ^ ι t) (fun t => (ι t : ℂ)) fun R hR => by
    obtain ⟨t, ht, htZ⟩ := hT.exists_notMem_finite
      ((finite_setOf_evalEval_natCast_pow_eq_zero hb hR).preimage hι.injOn)
    exact ⟨t, ht, htZ⟩

/-- `tail:lem:jetspan`: every infinite subfamily of the vectors `v_n` spans
`M^{(J+1)(K+1)}` over `M = ℂ(z)`. -/
theorem span_sourceJetVector_eq_top (J K : ℕ) {A : Set ℕ} (hA : A.Infinite) :
    span (RatFunc ℂ) (sourceJetVector J K '' A) = ⊤ :=
  span_jetVector_pow_eq_top halfFalling (fun j _ => halfFalling_ne_zero j) K (b := 2)
    (by simp) Function.injective_id hA

/-- `tail:lem:jetspan`, second sentence: every cofinite subfamily of every infinite
subfamily has full span. -/
theorem span_sourceJetVector_diff_eq_top (J K : ℕ) {A : Set ℕ} (hA : A.Infinite) {F : Set ℕ}
    (hF : F.Finite) : span (RatFunc ℂ) (sourceJetVector J K '' (A \ F)) = ⊤ :=
  span_sourceJetVector_eq_top J K (hA.sdiff hF)

/-- `tail:lem:jetspan` in the form of the hypothesis of `tail:lem:multilinear`
(`TailSpan.multilinear_baseChange_eq_zero`): the subfamily indexed by an infinite `A`
spans after every finite deletion. -/
theorem span_sourceJetVector_compl_eq_top (J K : ℕ) {A : Set ℕ} (hA : A.Infinite)
    (F : Finset A) :
    span (RatFunc ℂ) ((fun n : A => sourceJetVector J K n) '' (↑F : Set A)ᶜ) = ⊤ := by
  haveI := hA.to_subtype
  exact span_jetVector_pow_eq_top halfFalling (fun j _ => halfFalling_ne_zero j) K (b := 2)
    (by simp) Subtype.val_injective F.finite_toSet.infinite_compl

/-- `tail:lem:jetspan`, cofinite-span form: the cofinite span `TailSpan.cofiniteSpan` of
every infinite subfamily is the whole space. -/
theorem cofiniteSpan_sourceJetVector_eq_top (J K : ℕ) {A : Set ℕ} (hA : A.Infinite) :
    TailSpan.cofiniteSpan (M := RatFunc ℂ) (fun n : A => sourceJetVector J K n) = ⊤ :=
  iInf_eq_top.2 fun F => span_sourceJetVector_compl_eq_top J K hA F

end Surreal.TailAnalytic
