import FabiusFunction.QBinomialTheoremInfinite

/-!
# Uniform bounds for finite q-Pochhammer symbols and their reciprocals

For `‖q‖ < 1` the finite symbols `(a;q)_n` are bounded uniformly in `n` by
the real product `(-‖a‖;‖q‖)_∞`, and so is the infinite product `(a;q)_∞`.
When the infinite product does not vanish, its prefixes have reciprocals
bounded uniformly in `n` as well:

`‖(a;q)_n‖⁻¹ ≤ (-‖a‖;‖q‖)_∞ / ‖(a;q)_∞‖`,

because `(a;q)_∞ = (a;q)_n (aq^n;q)_∞` and the tail is bounded by
`(-‖a‖;‖q‖)_∞`.  These are the estimates that make every basic
hypergeometric series with nonvanishing denominator parameters dominated by a
geometric series, and hence absolutely convergent in the unit disc.

## Main declarations

* `qPochhammerInfIn_neg_le_neg`: monotonicity of `x ↦ (-x;r)_∞` on `x ≥ 0`.
* `norm_qPochhammerInfIn_le`: `‖(a;q)_∞‖ ≤ (-‖a‖;‖q‖)_∞`.
* `finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero`: prefixes of a
  nonvanishing product are nonvanishing.
* `inv_norm_finiteQPochhammerIn_le`: the uniform bound on the reciprocals.
* `exists_norm_finiteQPochhammerIn_div_le`: `(a;q)_n/(c;q)_n` is bounded in `n`.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-- For `0 ≤ x' ≤ x` and `0 ≤ r < 1`, `(-x';r)_∞ ≤ (-x;r)_∞`. -/
theorem qPochhammerInfIn_neg_le_neg {x x' r : ℝ} (hx' : 0 ≤ x') (hxx' : x' ≤ x) (hr0 : 0 ≤ r)
    (hr : r < 1) : qPochhammerInfIn (-x') r ≤ qPochhammerInfIn (-x) r := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  refine le_of_tendsto_of_tendsto' (tendsto_finiteQPochhammerIn_qPochhammerInfIn (-x') hr')
    (tendsto_finiteQPochhammerIn_qPochhammerInfIn (-x) hr') fun n => ?_
  unfold finiteQPochhammerIn
  refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
  · have := pow_nonneg hr0 j
    nlinarith
  · have := pow_nonneg hr0 j
    nlinarith

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- `‖(a;q)_∞‖ ≤ (-‖a‖;‖q‖)_∞`. -/
theorem norm_qPochhammerInfIn_le (a : 𝕜) {q : 𝕜} (hq : ‖q‖ < 1) :
    ‖qPochhammerInfIn a q‖ ≤ qPochhammerInfIn (-‖a‖) ‖q‖ := by
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  exact le_of_tendsto_of_tendsto' (tendsto_finiteQPochhammerIn_qPochhammerInfIn a hq).norm
    (tendsto_finiteQPochhammerIn_qPochhammerInfIn (-‖a‖) hq')
    fun n => norm_finiteQPochhammerIn_le_neg_norm a q n

/-- Every finite prefix of a nonvanishing infinite product is nonvanishing. -/
theorem finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (a : 𝕜) {q : 𝕜} (hq : ‖q‖ < 1)
    (h : qPochhammerInfIn a q ≠ 0) (n : ℕ) : finiteQPochhammerIn a q n ≠ 0 := by
  rw [qPochhammerInfIn_eq_finite_mul_shift a hq n] at h
  exact left_ne_zero_of_mul h

/-- **Uniform bound on the reciprocals of the prefixes** of a nonvanishing product:
`‖(a;q)_n‖⁻¹ ≤ (-‖a‖;‖q‖)_∞ / ‖(a;q)_∞‖` for every `n`. -/
theorem inv_norm_finiteQPochhammerIn_le (a : 𝕜) {q : 𝕜} (hq : ‖q‖ < 1)
    (h : qPochhammerInfIn a q ≠ 0) (n : ℕ) :
    ‖finiteQPochhammerIn a q n‖⁻¹ ≤ qPochhammerInfIn (-‖a‖) ‖q‖ / ‖qPochhammerInfIn a q‖ := by
  have hpos : 0 < ‖finiteQPochhammerIn a q n‖ :=
    norm_pos_iff.mpr (finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero a hq h n)
  have hN : 0 < ‖qPochhammerInfIn a q‖ := norm_pos_iff.mpr h
  have hle : ‖qPochhammerInfIn a q‖ ≤
      ‖finiteQPochhammerIn a q n‖ * qPochhammerInfIn (-‖a‖) ‖q‖ := by
    rw [qPochhammerInfIn_eq_finite_mul_shift a hq n, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_qPochhammerInfIn_le _ hq).trans ?_) (norm_nonneg _)
    refine qPochhammerInfIn_neg_le_neg (norm_nonneg _) ?_ (norm_nonneg q) hq
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg a) (pow_le_one₀ (norm_nonneg q) hq.le)
  rw [inv_le_iff_one_le_mul₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hN, one_mul, mul_comm]
  exact hle

/-- The quotients `(a;q)_n / (c;q)_n` are bounded uniformly in `n` whenever
`(c;q)_∞ ≠ 0`. -/
theorem exists_norm_finiteQPochhammerIn_div_le (a : 𝕜) {q : 𝕜} (hq : ‖q‖ < 1) {c : 𝕜}
    (hc : qPochhammerInfIn c q ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖finiteQPochhammerIn a q n / finiteQPochhammerIn c q n‖ ≤ K := by
  refine ⟨qPochhammerInfIn (-‖a‖) ‖q‖ * (qPochhammerInfIn (-‖c‖) ‖q‖ / ‖qPochhammerInfIn c q‖),
    ?_, fun n => ?_⟩
  · exact (norm_nonneg _).trans ((norm_div _ _).le.trans (mul_le_mul (norm_finiteQPochhammerIn_le a hq 0)
      (by rw [div_eq_mul_inv]; exact inv_norm_finiteQPochhammerIn_le c hq hc 0)
      (inv_nonneg.mpr (norm_nonneg _)) ((norm_nonneg _).trans (norm_finiteQPochhammerIn_le a hq 0))))
  · rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul (norm_finiteQPochhammerIn_le a hq n) (inv_norm_finiteQPochhammerIn_le c hq hc n)
      (inv_nonneg.mpr (norm_nonneg _)) ((norm_nonneg _).trans (norm_finiteQPochhammerIn_le a hq 0))

end Fabius
