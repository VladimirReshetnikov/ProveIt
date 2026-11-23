import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Cumulative interpolation with clipped ramps -/

namespace GlobeFlattening

noncomputable section

def clippedRamp (length x : ℝ) : ℝ := max (min x length) 0

theorem clippedRamp_mono (length : ℝ) : Monotone (clippedRamp length) :=
  fun _ _ h => max_le_max (min_le_min_right _ h) le_rfl

theorem clippedRamp_of_nonpos {length x : ℝ} (hx : x ≤ 0) :
    clippedRamp length x = 0 :=
  max_eq_right ((min_le_left _ _).trans hx)

theorem clippedRamp_of_length_le {length x : ℝ} (hlen : 0 ≤ length) (hx : length ≤ x) :
    clippedRamp length x = length := by
  unfold clippedRamp
  rw [min_eq_right hx, max_eq_left hlen]

/-- A continuous weight rising from zero to one across one latitude layer. -/
def rampWeight (start width y : ℝ) : ℝ :=
  clippedRamp width (y - start) / width

theorem rampWeight_eq_zero {start width y : ℝ} (hy : y ≤ start) :
    rampWeight start width y = 0 := by
  simp [rampWeight, clippedRamp_of_nonpos (sub_nonpos.mpr hy)]

theorem rampWeight_eq_one {start width y : ℝ}
    (hw : 0 < width) (hy : start + width ≤ y) :
    rampWeight start width y = 1 := by
  simp [rampWeight, clippedRamp_of_length_le hw.le (by linarith : width ≤ y - start),
    hw.ne']

theorem rampWeight_bounds {start width y : ℝ} (hw : 0 < width) :
    0 ≤ rampWeight start width y ∧ rampWeight start width y ≤ 1 := by
  unfold rampWeight clippedRamp
  constructor
  · exact div_nonneg (le_max_right _ _) hw.le
  · rw [div_le_iff₀ hw, one_mul]
    exact max_le (min_le_right (y - start) width) hw.le


theorem rampWeight_mono (start width : ℝ) (hw : 0 ≤ width) :
    Monotone (rampWeight start width) :=
  fun _ _ h => div_le_div_of_nonneg_right (clippedRamp_mono _ (sub_le_sub_right h _)) hw

/-- Interpolate between consecutive heights by adding each weighted rise. -/
def rampProfile (count : ℕ) (height weight : ℕ → ℝ) : ℝ :=
  height 0 + ∑ j ∈ Finset.range count, weight j * (height (j + 1) - height j)

private theorem rampProfile_truncate {count j : ℕ} {height weight : ℕ → ℝ} (hj : j ≤ count)
    (hw : ∀ i < count, j ≤ i → weight i = 0) :
    rampProfile j height weight = rampProfile count height weight := by
  unfold rampProfile
  congr 1
  apply Finset.sum_subset (Finset.range_mono hj)
  intro i hi hj'
  simp [hw i (Finset.mem_range.mp hi) (le_of_not_gt (Finset.mem_range.not.mp hj'))]

theorem rampProfile_at_core {count j : ℕ} {height weight : ℕ → ℝ} (hj : j ≤ count)
    (before : ∀ i < j, weight i = 1) (after : ∀ i < count, j ≤ i → weight i = 0) :
    rampProfile count height weight = height j := by
  rw [← rampProfile_truncate hj after]
  unfold rampProfile
  have htel : (∑ i ∈ Finset.range j, weight i * (height (i + 1) - height i)) =
      height j - height 0 := by
    rw [← Finset.sum_range_sub height j]
    exact Finset.sum_congr rfl fun i hi => by simp [before i (Finset.mem_range.mp hi)]
  rw [htel]
  ring

theorem rampProfile_at_layer {count j : ℕ} {height weight : ℕ → ℝ} (hj : j < count)
    (before : ∀ i < j, weight i = 1) (after : ∀ i < count, j < i → weight i = 0) :
    rampProfile count height weight =
      height j + weight j * (height (j + 1) - height j) := by
  rw [← rampProfile_truncate (Nat.succ_le_of_lt hj) (fun i hi hji => after i hi hji)]
  have hcore : rampProfile j height weight = height j :=
    rampProfile_at_core le_rfl before (fun _ hi hji => (not_lt_of_ge hji hi).elim)
  unfold rampProfile at *
  rw [Finset.sum_range_succ, ← add_assoc, hcore]

/-- A rising sequence of heights and rising ramp weights produce a rising
profile. The hypotheses only involve the rises used by the sum. -/
theorem rampProfile_mono_weight {count : ℕ} {height w₁ w₂ : ℕ → ℝ}
    (hheight : ∀ j < count, height j ≤ height (j + 1))
    (hweight : ∀ j < count, w₁ j ≤ w₂ j) :
    rampProfile count height w₁ ≤ rampProfile count height w₂ := by
  unfold rampProfile
  apply add_le_add le_rfl (Finset.sum_le_sum fun i hi => ?_)
  exact mul_le_mul_of_nonneg_right (hweight i (Finset.mem_range.mp hi))
    (sub_nonneg.mpr (hheight i (Finset.mem_range.mp hi)))

end

end GlobeFlattening
