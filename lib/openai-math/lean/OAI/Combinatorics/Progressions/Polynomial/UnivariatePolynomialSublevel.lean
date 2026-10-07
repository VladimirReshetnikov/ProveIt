import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.Combinatorics.Progressions.Estimates.SeparatedInterpolationBound
import OAI.Combinatorics.Progressions.Estimates.SeparatedRealSamples

namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped BigOperators

def unitPolynomialSublevel (p : ℝ[X]) (u : ℝ) : Set ℝ :=
  {x | |x| ≤ 1 ∧ |p.eval x| ≤ u}

theorem unitPolynomialSublevel_measurable (p : ℝ[X]) (u : ℝ) :
    MeasurableSet (unitPolynomialSublevel p u) :=
  ((isClosed_le continuous_abs continuous_const).inter
    (isClosed_le p.continuous.abs continuous_const)).measurableSet

theorem unitPolynomialSublevel_volume_ne_top (p : ℝ[X]) (u : ℝ) :
    volume (unitPolynomialSublevel p u) ≠ ⊤ := by
  apply measure_ne_top_of_subset (s := Set.Icc (-1 : ℝ) 1) _ (by simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])
  intro x hx
  exact abs_le.mp hx.1

theorem unitPolynomialSublevel_power_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    |p.coeff k| * (volume.real (unitPolynomialSublevel p u)) ^ d ≤
      (d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d * u := by
  let mass := volume.real (unitPolynomialSublevel p u)
  change |p.coeff k| * mass ^ d ≤ _
  have hmass0 : 0 ≤ mass := measureReal_nonneg
  by_cases hz : mass = 0
  · rw [hz, zero_pow (Nat.ne_of_gt hd), mul_zero]
    positivity
  have hmass : 0 < mass := lt_of_le_of_ne hmass0 (Ne.symm hz)
  let r := mass / (4 * (d + 1 : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : 2 * (d + 1 : ℝ) * r = mass / 2 := by
    dsimp [r]
    field_simp
    ring
  have hlarge : 2 * ((d + 1 : ℕ) : ℝ) * r < volume.real (unitPolynomialSublevel p u) := by
    push_cast
    rw [hscale]
    change mass / 2 < mass
    linarith
  obtain ⟨t, htcard, hts, htsep⟩ := exists_separated_real_samples (unitPolynomialSublevel p u) hr (d + 1) hlarge
  have hdegree : p.degree < t.card := by
    rw [htcard]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hcoeff := polynomial_coeff_le_of_separated_samples p t hr hu hdegree
    (fun x hx => (hts hx).1) (fun x hx => (hts hx).2) htsep k
  rw [htcard, Nat.add_sub_cancel] at hcoeff
  push_cast at hcoeff
  have hcancel : (2 / r) * mass = 8 * (d + 1 : ℝ) := by
    dsimp [r]
    field_simp
    ring
  calc
    |p.coeff k| * mass ^ d ≤ ((d + 1 : ℝ) * u * (2 / r) ^ d) * mass ^ d :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hmass0 d)
    _ = (d + 1 : ℝ) * u * ((2 / r) * mass) ^ d := by rw [mul_pow]; ring
    _ = _ := by rw [hcancel]; ring

noncomputable def univariateSublevelConstant (d : ℕ) : ℝ :=
  ((d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d) ^ ((d : ℝ)⁻¹)

theorem univariateSublevelConstant_pos (d : ℕ) : 0 < univariateSublevelConstant d := by
  unfold univariateSublevelConstant
  positivity

theorem unitPolynomialSublevel_rpow_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (k : ℕ) (hk : c ≤ |p.coeff k|) :
    volume.real (unitPolynomialSublevel p u) ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  unfold univariateSublevelConstant
  rw [← Real.mul_rpow (by positivity : 0 ≤ (d + 1 : ℝ) * (8 * (d + 1 : ℝ)) ^ d)
    (div_nonneg hu hc.le)]
  apply (Real.le_rpow_inv_iff_of_pos measureReal_nonneg (by positivity)
    (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  rw [Real.rpow_natCast, ← mul_div_assoc]
  apply (le_div_iff₀ hc).mpr
  calc
    (volume.real (unitPolynomialSublevel p u)) ^ d * c ≤
        |p.coeff k| * (volume.real (unitPolynomialSublevel p u)) ^ d := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hk (pow_nonneg measureReal_nonneg d)
    _ ≤ _ := unitPolynomialSublevel_power_bound p hd hdeg hu k

end Erdos3

end

end OAI
