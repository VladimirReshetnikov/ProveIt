import FabiusFunction.JacobiTripleProduct
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Jacobi's cubic identity

`(q;q)_∞³ = ∑_{n≥0} (-1)^n (2n+1) q^{n(n+1)/2}` for `‖q‖ < 1`.

The classical proof differentiates Jacobi's triple product at `z = 1`.  Here
the derivative is replaced by a **difference quotient and Tannery's theorem**:
pairing `k = n+1` with `k = -n` in the triple product (both have
`k(k-1)/2 = n(n+1)/2`) gives, for `z ≠ 0, 1`,

`(z;q)_∞ (q/z;q)_∞ (q;q)_∞ / (1-z) = ∑_{n≥0} (-1)^{n+1} q^{\binom{n+1}{2}} · (-(z^{-n} ∑_{i<2n+1} z^i))`,

because `z^{n+1} - z^{-n} = -z^{-n}(1 - z^{2n+1})` and `1 - z^{2n+1} = (1-z)∑_{i<2n+1} z^i`.
The left side is `(zq;q)_∞ (q/z;q)_∞ (q;q)_∞ → (q;q)_∞³` as `z → 1`; on the
right each term tends to `(-1)^n (2n+1) q^{\binom{n+1}{2}}`, and near `z = 1`
the terms are dominated by `‖q‖^{\binom n2} (27‖q‖/2)^n`, so the limit passes
inside the sum.

## Main declarations

* `two_mul_add_one_le_three_pow`: `2n+1 ≤ 3^n`.
* `hasSum_jacobi_cubic`: Jacobi's identity in `HasSum` form.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

/-- `2n + 1 ≤ 3^n`. -/
theorem two_mul_add_one_le_three_pow (n : ℕ) : 2 * n + 1 ≤ 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- **Jacobi's cubic identity**: for `‖q‖ < 1`,
`∑_{n≥0} (-1)^n (2n+1) q^{\binom{n+1}{2}} = (q;q)_∞³`. -/
theorem hasSum_jacobi_cubic {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n + 1).choose 2)
      (qPochhammerInfIn q q ^ 3) := by
  -- the paired difference quotients
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℕ → ℂ, ∀ z n, T z n =
      (-1 : ℂ) ^ (n + 1) * q ^ (n + 1).choose 2 *
        (-((z ^ n)⁻¹ * ∑ i ∈ Finset.range (2 * n + 1), z ^ i)) := ⟨_, fun _ _ => rfl⟩
  -- Step A: pair `k = n+1` with `k = -n` in the triple product
  have hA : ∀ z : ℂ, z ≠ 0 → HasSum (fun n : ℕ =>
      (-1 : ℂ) ^ ((n : ℤ) + 1) * q ^ thetaExponent ((n : ℤ) + 1) * z ^ ((n : ℤ) + 1) +
        (-1 : ℂ) ^ (-(n : ℤ)) * q ^ thetaExponent (-(n : ℤ)) * z ^ (-(n : ℤ)))
      (qPochhammerInfIn z q * qPochhammerInfIn (q / z) q * qPochhammerInfIn q q) := by
    intro z hz
    have h := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr (hasSum_jacobi_triple_product hq hz)
    refine h.nat_add_neg_add_one.congr_fun fun n => ?_
    simp only [Function.comp_apply, Equiv.coe_addRight]
    rw [show (-((n : ℤ) + 1) + 1) = -(n : ℤ) by ring]
  -- Step B: the closed form of each paired term divided by `1 - z`
  have hB : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → ∀ n : ℕ,
      ((-1 : ℂ) ^ ((n : ℤ) + 1) * q ^ thetaExponent ((n : ℤ) + 1) * z ^ ((n : ℤ) + 1) +
        (-1 : ℂ) ^ (-(n : ℤ)) * q ^ thetaExponent (-(n : ℤ)) * z ^ (-(n : ℤ))) / (1 - z) =
      T z n := by
    intro z hz hz1 n
    have hzn : z ^ n ≠ 0 := pow_ne_zero n hz
    have hg := mul_neg_geom_sum z (2 * n + 1)
    have hz' : z ^ (2 * n + 1) * (z ^ n)⁻¹ = z ^ (n + 1) := by
      rw [show 2 * n + 1 = (n + 1) + n by ring, pow_add, mul_inv_cancel_right₀ hzn]
    rw [hT, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, thetaExponent_natCast,
      thetaExponent_neg_natCast, zpow_natCast, zpow_natCast, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, show ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n by rw [← inv_pow, inv_neg, inv_one],
      div_eq_iff (sub_ne_zero.mpr (Ne.symm hz1))]
    linear_combination ((-1 : ℂ) ^ (n + 1) * q ^ (n + 1).choose 2 * (z ^ n)⁻¹) * hg +
      (-((-1 : ℂ) ^ (n + 1) * q ^ (n + 1).choose 2)) * hz'
  -- Step C: the paired series sums to the product with `(z;q)_∞` replaced by `(zq;q)_∞`
  have hC : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → ∑' n : ℕ, T z n =
      qPochhammerInfIn (z * q) q * (qPochhammerInfIn (q / z) q * qPochhammerInfIn q q) := by
    intro z hz hz1
    have h := ((hA z hz).div_const (1 - z)).congr_fun fun n => (hB z hz hz1 n).symm
    rw [h.tsum_eq, qPochhammerInfIn_succ_shift z hq, mul_assoc, mul_assoc,
      mul_div_cancel_left₀ _ (sub_ne_zero.mpr (Ne.symm hz1))]
  -- Step D: termwise limits at `z = 1`
  have hD : ∀ n : ℕ, Tendsto (fun z : ℂ => T z n) (𝓝[≠] 1)
      (𝓝 ((-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n + 1).choose 2)) := by
    intro n
    have h1 : ContinuousAt (fun z : ℂ => (z ^ n)⁻¹) 1 :=
      (continuous_pow n).continuousAt.inv₀ (by simp)
    have h2 : Continuous (fun z : ℂ => ∑ i ∈ Finset.range (2 * n + 1), z ^ i) :=
      continuous_finsetSum _ fun i _ => continuous_pow i
    have hc : ContinuousAt (fun z : ℂ => T z n) 1 := by
      simp only [hT]
      exact continuousAt_const.mul ((h1.mul h2.continuousAt).neg)
    have hval : T 1 n = (-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n + 1).choose 2 := by
      rw [hT]
      simp only [one_pow, inv_one, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
      push_cast
      ring
    rw [← hval]
    exact tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto
  -- Step E: domination near `z = 1`
  have hE : ∀ᶠ z in 𝓝[≠] (1 : ℂ), ∀ n : ℕ,
      ‖T z n‖ ≤ ‖q‖ ^ n.choose 2 * (‖q‖ * (27 / 2)) ^ n := by
    have hball : Metric.ball (1 : ℂ) (1 / 2) ∈ 𝓝[≠] (1 : ℂ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 1 (by norm_num))
    filter_upwards [hball] with z hz n
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hz_le : ‖z‖ ≤ 3 / 2 := by
      calc ‖z‖ = ‖(z - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 / 2 := by rw [norm_one]; linarith
    have hz_ge : 2⁻¹ ≤ ‖z‖ := by
      have := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one, norm_sub_rev] at this
      have h12 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [h12]
      linarith
    have hzn : (‖z‖ ^ n)⁻¹ ≤ 2 ^ n := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z))
        (inv_le_of_inv_le₀ (by norm_num) hz_ge) n
    have hS : ‖∑ i ∈ Finset.range (2 * n + 1), z ^ i‖ ≤ (2 * n + 1) * (3 / 2 : ℝ) ^ (2 * n) := by
      calc ‖∑ i ∈ Finset.range (2 * n + 1), z ^ i‖
          ≤ ∑ i ∈ Finset.range (2 * n + 1), ‖z ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (2 * n + 1), (3 / 2 : ℝ) ^ (2 * n) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_pow]
            calc ‖z‖ ^ i ≤ (3 / 2) ^ i := pow_le_pow_left₀ (norm_nonneg z) hz_le i
              _ ≤ (3 / 2) ^ (2 * n) :=
                  pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        _ = (2 * n + 1) * (3 / 2 : ℝ) ^ (2 * n) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have h3 : (2 * n + 1 : ℝ) ≤ 3 ^ n := by exact_mod_cast two_mul_add_one_le_three_pow n
    have hpow : (2 : ℝ) ^ n * (3 ^ n * (3 / 2) ^ (2 * n)) = (27 / 2) ^ n := by
      rw [pow_mul, ← mul_pow, ← mul_pow]
      norm_num
    have hnorm : ‖T z n‖ = ‖q‖ ^ (n + 1).choose 2 *
        ((‖z‖ ^ n)⁻¹ * ‖∑ i ∈ Finset.range (2 * n + 1), z ^ i‖) := by
      rw [hT]
      simp only [norm_mul, norm_neg, norm_pow, norm_inv, norm_one, one_pow, one_mul]
    rw [hnorm, Nat.choose_succ_succ' n 1, Nat.choose_one_right, pow_add, mul_pow]
    calc ‖q‖ ^ n * ‖q‖ ^ n.choose 2 * ((‖z‖ ^ n)⁻¹ * ‖∑ i ∈ Finset.range (2 * n + 1), z ^ i‖)
        ≤ ‖q‖ ^ n * ‖q‖ ^ n.choose 2 * (2 ^ n * ((2 * n + 1) * (3 / 2 : ℝ) ^ (2 * n))) := by
          gcongr
      _ ≤ ‖q‖ ^ n * ‖q‖ ^ n.choose 2 * (2 ^ n * (3 ^ n * (3 / 2 : ℝ) ^ (2 * n))) := by
          gcongr
      _ = ‖q‖ ^ n.choose 2 * (‖q‖ ^ n * (27 / 2) ^ n) := by rw [hpow]; ring
  -- Step F: Tannery's theorem and the limit of the product side
  have hbound : Summable fun n : ℕ => ‖q‖ ^ n.choose 2 * (‖q‖ * (27 / 2)) ^ n :=
    summable_pow_choose_two_mul_pow (norm_nonneg q) hq (by positivity)
  have hTan := tendsto_tsum_of_dominated_convergence hbound hD hE
  have hprod : Tendsto (fun z : ℂ => qPochhammerInfIn (z * q) q *
      (qPochhammerInfIn (q / z) q * qPochhammerInfIn q q)) (𝓝[≠] 1)
      (𝓝 (qPochhammerInfIn q q ^ 3)) := by
    have hc : ContinuousAt (fun z : ℂ => qPochhammerInfIn (z * q) q *
        (qPochhammerInfIn (q / z) q * qPochhammerInfIn q q)) 1 := by
      have h1 : ContinuousAt (fun z : ℂ => qPochhammerInfIn (z * q) q) 1 :=
        (continuous_qPochhammerInfIn hq).continuousAt.comp (continuousAt_id.mul continuousAt_const)
      have h2 : ContinuousAt (fun z : ℂ => qPochhammerInfIn (q / z) q) 1 :=
        (continuous_qPochhammerInfIn hq).continuousAt.comp
          (continuousAt_const.div continuousAt_id one_ne_zero)
      exact h1.mul (h2.mul continuousAt_const)
    have hval : qPochhammerInfIn (1 * q) q * (qPochhammerInfIn (q / 1) q * qPochhammerInfIn q q) =
        qPochhammerInfIn q q ^ 3 := by
      rw [one_mul, div_one, pow_three]
    rw [← hval]
    exact tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto
  have hTan' : Tendsto (fun z : ℂ => ∑' n : ℕ, T z n) (𝓝[≠] 1) (𝓝 (qPochhammerInfIn q q ^ 3)) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin, (eventually_ne_nhds one_ne_zero).filter_mono
      nhdsWithin_le_nhds] with z hz1 hz0
    exact (hC z hz0 hz1).symm
  have hgs : Summable fun n : ℕ => (-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n + 1).choose 2 :=
    hbound.of_norm_bounded fun n => le_of_tendsto (hD n).norm (hE.mono fun z hz => hz n)
  rw [← tendsto_nhds_unique hTan hTan']
  exact hgs.hasSum

end Fabius
