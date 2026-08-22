import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Matched dyadic--triadic gap amplification

This module proves the exact one-gap inequality behind the comparison of synchronized
dyadic and triadic near-power products.  Its reusable calculus core says that, for `p > 1`,
the unit increment `(x + 1) ^ p - x ^ p` is strictly increasing on the nonnegative reals.
Specializing to `p = log 3 / log 2` gives both the exponential and logarithmic forms of the
strict matched-gap bound.  A finite-product theorem records the resulting amplification
without assuming any orbit, floor, or equidistribution input.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The increment of the real `p`-power over a unit interval. -/
def unitRpowGap (p x : ℝ) : ℝ := (x + 1) ^ p - x ^ p

/-- For exponent greater than one, unit real-power increments strictly increase on the
nonnegative half-line. -/
theorem strictMonoOn_unitRpowGap {p : ℝ} (hp : 1 < p) :
    StrictMonoOn (unitRpowGap p) (Ici 0) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0 : ℝ))
    (f' := fun x ↦ p * (x + 1) ^ (p - 1) - p * x ^ (p - 1))
  · exact ((Real.continuous_rpow_const hp0).comp
        (continuous_id.add continuous_const)).sub
      (Real.continuous_rpow_const hp0) |>.continuousOn
  · intro x hx
    rw [interior_Ici]
    have hinner : HasDerivAt (fun y : ℝ ↦ y + 1) 1 x := by
      simpa using (hasDerivAt_id x).add_const 1
    have hderiv :=
      (hinner.rpow_const (p := p) (Or.inr hp.le)).sub
        (Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inr hp.le))
    have heq : unitRpowGap p =ᶠ[nhds x]
        ((fun y : ℝ ↦ (y + 1) ^ p) - fun y : ℝ ↦ y ^ p) := by
      filter_upwards with y
      rfl
    have hderiv' : HasDerivAt (unitRpowGap p)
        (p * (x + 1) ^ (p - 1) - p * x ^ (p - 1)) x := by
      apply (hderiv.congr_of_eventuallyEq heq).congr_deriv
      ring
    exact hderiv'.hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 ≤ x := hx.le
    have hx1 : x < x + 1 := by linarith
    have hpow : x ^ (p - 1) < (x + 1) ^ (p - 1) :=
      Real.strictMonoOn_rpow_Ici_of_exponent_pos (sub_pos.mpr hp)
        hx0 (add_nonneg hx0 (by norm_num)) hx1
    exact sub_pos.mpr (mul_lt_mul_of_pos_left hpow (lt_trans (by norm_num) hp))

/-- Comparison of a unit power increment at `1` with one farther along the positive axis. -/
theorem unitRpowGap_two_lt {p x : ℝ} (hp : 1 < p) (hx : 1 < x) :
    (2 : ℝ) ^ p - 1 < (x + 1) ^ p - x ^ p := by
  have h :=
    strictMonoOn_unitRpowGap hp (by norm_num) (le_trans (by norm_num) hx.le) hx
  norm_num [unitRpowGap] at h ⊢
  exact h

/-- Scale-free form of the matched-gap inequality for any exponent satisfying `2 ^ p = 3`. -/
theorem two_mul_rpow_lt_one_add_rpow_sub_one {p t : ℝ}
    (hp : 1 < p) (ht0 : 0 < t) (ht1 : t < 1) (h2p : (2 : ℝ) ^ p = 3) :
    2 * t ^ p < (1 + t) ^ p - 1 := by
  have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht0).mpr ht1
  have hgap := unitRpowGap_two_lt hp hinv
  rw [h2p] at hgap
  have htppos : 0 < t ^ p := Real.rpow_pos_of_pos ht0 _
  have hmul := mul_lt_mul_of_pos_right hgap htppos
  calc
    2 * t ^ p = (3 - 1) * t ^ p := by ring
    _ < (((t⁻¹ + 1) ^ p - (t⁻¹) ^ p) * t ^ p) := hmul
    _ = (1 + t) ^ p - 1 := by
      rw [sub_mul]
      rw [← Real.mul_rpow (by positivity : 0 ≤ t⁻¹ + 1) ht0.le]
      rw [← Real.mul_rpow (by positivity : 0 ≤ t⁻¹) ht0.le]
      field_simp
      simp

private theorem two_rpow_logRatio :
    (2 : ℝ) ^ logThreeDivLogTwo = 3 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), logThreeDivLogTwo]
  have hmul : Real.log (2 : ℝ) * (Real.log (3 : ℝ) / Real.log (2 : ℝ)) =
      Real.log (3 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

private theorem two_rpow_rpow_logRatio (u : ℝ) :
    ((2 : ℝ) ^ u) ^ logThreeDivLogTwo = (3 : ℝ) ^ u := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_logRatio]

/-- Strict amplification for one lower-branch synchronized dyadic--triadic gap. -/
theorem matched_one_gap_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    2 * ((2 : ℝ) ^ u - 1) ^ logThreeDivLogTwo < (3 : ℝ) ^ u - 1 := by
  have ht0 : 0 < (2 : ℝ) ^ u - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hu0)
  have hpowlt : (2 : ℝ) ^ u < (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hu1
  have ht1 : (2 : ℝ) ^ u - 1 < 1 := by
    rw [Real.rpow_one] at hpowlt
    linarith
  have h := two_mul_rpow_lt_one_add_rpow_sub_one
    one_lt_logThreeDivLogTwo ht0 ht1 two_rpow_logRatio
  rw [show (1 : ℝ) + ((2 : ℝ) ^ u - 1) = (2 : ℝ) ^ u by ring,
    two_rpow_rpow_logRatio] at h
  exact h

/-- The logarithmic `Phi` form of `matched_one_gap_bound`. -/
theorem phi_gt_logb_three_two {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Real.logb 3 ((3 : ℝ) ^ u - 1) - Real.logb 2 ((2 : ℝ) ^ u - 1) >
      Real.logb 3 2 := by
  let t : ℝ := (2 : ℝ) ^ u - 1
  let s : ℝ := (3 : ℝ) ^ u - 1
  have ht0 : 0 < t := by
    dsimp [t]
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) hu0)
  have hpow : 2 * t ^ logThreeDivLogTwo < s := by
    simpa [t, s] using matched_one_gap_bound hu0 hu1
  have htpow0 : 0 < t ^ logThreeDivLogTwo := Real.rpow_pos_of_pos ht0 _
  have hlog := Real.log_lt_log (mul_pos (by norm_num) htpow0) hpow
  rw [Real.log_mul (by norm_num) htpow0.ne', Real.log_rpow ht0] at hlog
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  rw [gt_iff_lt, Real.logb, Real.logb, Real.logb, lt_sub_iff_add_lt]
  have hrearrange :
      Real.log 2 / Real.log 3 + Real.log t / Real.log 2 =
        (Real.log 2 + logThreeDivLogTwo * Real.log t) / Real.log 3 := by
    rw [logThreeDivLogTwo]
    field_simp
  rw [hrearrange]
  exact (div_lt_div_iff_of_pos_right hlog3).2 hlog

/-- A strict pointwise matched-gap inequality amplifies over every nonempty finite product. -/
theorem prod_matched_gap_bound {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (dyadic triadic : ι → ℝ) (hindices : indices.Nonempty)
    (hdyadic : ∀ i ∈ indices, 0 < dyadic i)
    (hgap : ∀ i ∈ indices,
      2 * (dyadic i) ^ logThreeDivLogTwo < triadic i) :
    (2 : ℝ) ^ indices.card *
        (∏ i ∈ indices, dyadic i) ^ logThreeDivLogTwo <
      ∏ i ∈ indices, triadic i := by
  have hprod :
      (∏ i ∈ indices, 2 * (dyadic i) ^ logThreeDivLogTwo) <
        ∏ i ∈ indices, triadic i := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i hi
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (hdyadic i hi) _)
    · exact hgap
    · exact hindices
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Real.finsetProd_rpow indices dyadic (fun i hi ↦ (hdyadic i hi).le)] at hprod
  exact hprod

/-- Finite lower-branch product amplification, specialized to arbitrary phases in `(0,1)`. -/
theorem prod_matched_one_gap_bound {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (phase : ι → ℝ) (hindices : indices.Nonempty)
    (hphase : ∀ i ∈ indices, 0 < phase i ∧ phase i < 1) :
    (2 : ℝ) ^ indices.card *
        (∏ i ∈ indices, ((2 : ℝ) ^ phase i - 1)) ^ logThreeDivLogTwo <
      ∏ i ∈ indices, ((3 : ℝ) ^ phase i - 1) := by
  apply prod_matched_gap_bound indices
      (fun i ↦ (2 : ℝ) ^ phase i - 1)
      (fun i ↦ (3 : ℝ) ^ phase i - 1) hindices
  · intro i hi
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (hphase i hi).1)
  · intro i hi
    exact matched_one_gap_bound (hphase i hi).1 (hphase i hi).2

end

end LeanProofs.TwoBaseIntegerExponent
