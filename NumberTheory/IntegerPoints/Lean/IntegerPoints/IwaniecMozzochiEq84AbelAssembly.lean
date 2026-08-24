import IntegerPoints.IwaniecMozzochiEq84AbelPrefixes
import IntegerPoints.IwaniecMozzochiEq84SigmaVariation
import Mathlib.Tactic

/-!
# Abstract Abel assembly for Iwaniec--Mozzochi (8.4)

This module combines three already isolated inputs on the inclusive index
interval `0, ..., floor (8N)`:

* the `802 / sqrt beta` bound for every quadratic prefix;
* the endpoint and first-difference bounds for the fixed factor
  `(sigma (n / N) : Complex)`;
* the exact finite complex Abel inequality.

The second complex factor `v` remains completely abstract.  Its pointwise norm
bound and its literal finite first-difference sum are ordinary theorem
hypotheses.  No remainder estimate, phase-specific normalization, or opaque
proposition-valued premise is introduced here.
-/

open Real Set
open scoped BigOperators

namespace LeanProofs.IntegerPoints

/-! ## Exact sigma-variation scale -/

/-- Abel summation on the literal inclusive range `0, ..., floor (8N)`, with
an arbitrary second factor `v`.

The displayed summand is ordered as in the eventual equation (8.4):
`sigmaWeight * quadraticExponential * v`.  Internally it is rearranged to
`(sigmaWeight * v) * quadraticExponential`, so the pure quadratic sequence is
the sequence whose prefixes receive the `802 / sqrt beta` bound. -/
theorem section8_abel_sum_le_of_abstract_factor_bounds
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₀ S₁ : ℝ}
    (hS₀ : 0 ≤ S₀)
    (hsigmaBound : ∀ t ∈ Set.Icc (0 : ℝ) 8, |sigma t| ≤ S₀)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    (alpha beta N : ℝ) (hN : 1 ≤ N)
    (hbeta : 0 < beta) (hbetaN : beta * N ≤ 4)
    (v : ℕ → ℂ) (V DV : ℝ)
    (hv : ∀ i, i ≤ ⌊8 * N⌋₊ → ‖v i‖ ≤ V)
    (hdv : (∑ i ∈ Finset.range ⌊8 * N⌋₊, ‖v i - v (i + 1)‖) ≤ DV) :
    ‖∑ n ∈ Finset.range (⌊8 * N⌋₊ + 1),
        section8SigmaWeight sigma N n *
          e (section8QuadraticPhase alpha beta n) * v n‖ ≤
      (802 / Real.sqrt beta) *
        (S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) + S₀ * DV) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hprefix : ∀ i, i ≤ ⌊8 * N⌋₊ →
      ‖FiniteComplexAbel.prefixSum
          (fun n : ℕ ↦ e (section8QuadraticPhase alpha beta n)) i‖ ≤
        802 / Real.sqrt beta :=
    section8_quadratic_prefixSum_uniform alpha beta N hN hbeta hbetaN
  have hvariation :
      FiniteComplexAbel.variation
          (fun i ↦ section8SigmaWeight sigma N i * v i) ⌊8 * N⌋₊ ≤
        S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) + S₀ * DV := by
    calc
      FiniteComplexAbel.variation
          (fun i ↦ section8SigmaWeight sigma N i * v i) ⌊8 * N⌋₊ ≤
          S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) +
            S₀ * (∑ i ∈ Finset.range ⌊8 * N⌋₊, ‖v i - v (i + 1)‖) :=
        section8SigmaWeight_product_variation_le
          hsigma hsigmaBound hderiv hNpos v V hv
      _ ≤ S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) + S₀ * DV :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hdv hS₀)
  have hAbel := FiniteComplexAbel.norm_weighted_sum_le_variation
    (fun n : ℕ ↦ e (section8QuadraticPhase alpha beta n))
    (fun n : ℕ ↦ section8SigmaWeight sigma N n * v n)
    ⌊8 * N⌋₊ (802 / Real.sqrt beta) hprefix
  have hcoefficient : 0 ≤ 802 / Real.sqrt beta :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg beta)
  have hsum :
      (∑ n ∈ Finset.range (⌊8 * N⌋₊ + 1),
          section8SigmaWeight sigma N n *
            e (section8QuadraticPhase alpha beta n) * v n) =
        ∑ n ∈ Finset.range (⌊8 * N⌋₊ + 1),
          (section8SigmaWeight sigma N n * v n) *
            e (section8QuadraticPhase alpha beta n) := by
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hsum]
  exact hAbel.trans (mul_le_mul_of_nonneg_left hvariation hcoefficient)

/-! ## Scale-independent sigma-variation form -/

/-- The exact floor factor may be safely replaced by `8 * S₁` when the compact
derivative constant is nonnegative.  Nonnegativity of `V` is derived from its
stated endpoint bound rather than added as a redundant premise. -/
theorem section8_abel_sum_le_of_abstract_factor_bounds_eight
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₀ S₁ : ℝ}
    (hS₀ : 0 ≤ S₀) (hS₁ : 0 ≤ S₁)
    (hsigmaBound : ∀ t ∈ Set.Icc (0 : ℝ) 8, |sigma t| ≤ S₀)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    (alpha beta N : ℝ) (hN : 1 ≤ N)
    (hbeta : 0 < beta) (hbetaN : beta * N ≤ 4)
    (v : ℕ → ℂ) (V DV : ℝ)
    (hv : ∀ i, i ≤ ⌊8 * N⌋₊ → ‖v i‖ ≤ V)
    (hdv : (∑ i ∈ Finset.range ⌊8 * N⌋₊, ‖v i - v (i + 1)‖) ≤ DV) :
    ‖∑ n ∈ Finset.range (⌊8 * N⌋₊ + 1),
        section8SigmaWeight sigma N n *
          e (section8QuadraticPhase alpha beta n) * v n‖ ≤
      (802 / Real.sqrt beta) *
        (S₀ * V + V * (8 * S₁) + S₀ * DV) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hV : 0 ≤ V :=
    (norm_nonneg (v ⌊8 * N⌋₊)).trans (hv ⌊8 * N⌋₊ le_rfl)
  have hsigmaScale :
      (⌊8 * N⌋₊ : ℝ) * S₁ / N ≤ 8 * S₁ :=
    section8_floor_mul_deriv_div_le hNpos hS₁
  have hbracket :
      S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) + S₀ * DV ≤
        S₀ * V + V * (8 * S₁) + S₀ * DV :=
    add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsigmaScale hV)) le_rfl
  have hcoefficient : 0 ≤ 802 / Real.sqrt beta :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg beta)
  exact (section8_abel_sum_le_of_abstract_factor_bounds
    hsigma hS₀ hsigmaBound hderiv alpha beta N hN hbeta hbetaN v V DV hv hdv).trans
      (mul_le_mul_of_nonneg_left hbracket hcoefficient)

/-! ## Existing Section 8 range notation -/

/-- The exact-bound theorem rewritten with the already established notation
`section8WeightRange N = range (floor (8N) + 1)`. -/
theorem section8_weightRange_abel_sum_le_of_abstract_factor_bounds
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) {S₀ S₁ : ℝ}
    (hS₀ : 0 ≤ S₀)
    (hsigmaBound : ∀ t ∈ Set.Icc (0 : ℝ) 8, |sigma t| ≤ S₀)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 8, |deriv sigma t| ≤ S₁)
    (alpha beta N : ℝ) (hN : 1 ≤ N)
    (hbeta : 0 < beta) (hbetaN : beta * N ≤ 4)
    (v : ℕ → ℂ) (V DV : ℝ)
    (hv : ∀ i, i ≤ ⌊8 * N⌋₊ → ‖v i‖ ≤ V)
    (hdv : (∑ i ∈ Finset.range ⌊8 * N⌋₊, ‖v i - v (i + 1)‖) ≤ DV) :
    ‖∑ n ∈ section8WeightRange N,
        section8SigmaWeight sigma N n *
          e (section8QuadraticPhase alpha beta n) * v n‖ ≤
      (802 / Real.sqrt beta) *
        (S₀ * V + V * ((⌊8 * N⌋₊ : ℝ) * S₁ / N) + S₀ * DV) := by
  simpa only [section8WeightRange] using
    section8_abel_sum_le_of_abstract_factor_bounds
      hsigma hS₀ hsigmaBound hderiv alpha beta N hN hbeta hbetaN v V DV hv hdv

end LeanProofs.IntegerPoints
