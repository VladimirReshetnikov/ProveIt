import GlobeFlattening.CellProfile
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous longitude profiles across a row of cells

A clipped ramp accounts for the extra rise on each short segment. Summing
these ramps avoids choosing an interval at a grid point. The sum telescopes
at grid points and agrees with the single-cell formula on each closed cell.
-/

open scoped BigOperators

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

def meshPoint (left width : ℝ) (j : ℕ) : ℝ := left + j * width

theorem meshPoint_succ (left width : ℝ) (j : ℕ) :
    meshPoint left width (j + 1) = meshPoint left width j + width := by
  unfold meshPoint
  push_cast
  ring

theorem meshPoint_mono {left width : ℝ} (hwidth : 0 ≤ width) :
    Monotone (meshPoint left width) :=
  fun _ _ h => add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) hwidth)

def stripProfile (left width cut slope : ℝ) (count : ℕ) (old : ℝ → ℝ) (x : ℝ) : ℝ :=
  old left + slope * (x - left) +
    ∑ j ∈ Finset.range count,
      (catchUpSlope width cut slope
        (old (meshPoint left width (j + 1)) - old (meshPoint left width j)) - slope) *
        clippedRamp (width - cut) (x - (meshPoint left width j + cut))

theorem continuous_stripProfile (left width cut slope : ℝ)
    (count : ℕ) (old : ℝ → ℝ) :
    Continuous (stripProfile left width cut slope count old) := by
  unfold stripProfile clippedRamp
  fun_prop

/-- The lower slope extends across any number of cells. Only the rises at
grid points of the old profile enter the hypotheses. -/
theorem stripProfile_lower_slope {left width cut slope : ℝ} {count : ℕ} {old : ℝ → ℝ}
    (hcut : cut < width)
    (hrise : ∀ j < count, slope * width ≤
      old (meshPoint left width (j + 1)) - old (meshPoint left width j))
    {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) :
    slope * (x₂ - x₁) ≤
      stripProfile left width cut slope count old x₂ -
        stripProfile left width cut slope count old x₁ := by
  have hramps : ∑ j ∈ Finset.range count,
      (catchUpSlope width cut slope
        (old (meshPoint left width (j + 1)) - old (meshPoint left width j)) - slope) *
        clippedRamp (width - cut) (x₁ - (meshPoint left width j + cut))
      ≤ ∑ j ∈ Finset.range count,
      (catchUpSlope width cut slope
        (old (meshPoint left width (j + 1)) - old (meshPoint left width j)) - slope) *
        clippedRamp (width - cut) (x₂ - (meshPoint left width j + cut)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (clippedRamp_mono _ (sub_le_sub_right hx _))
      (sub_nonneg.mpr (le_catchUpSlope hcut (hrise j (Finset.mem_range.mp hj))))
  unfold stripProfile
  linarith


/-- On the closed cell at index `j`, the continuous strip profile is the
single-cell profile translated to the old value at the left grid point. -/
theorem stripProfile_eq_cellProfile {left width cut slope : ℝ} {count j : ℕ}
    {old : ℝ → ℝ} {x : ℝ} (hcut₀ : 0 ≤ cut) (hcut : cut < width)
    (hj : j < count) (hx₁ : meshPoint left width j ≤ x)
    (hx₂ : x ≤ meshPoint left width (j + 1)) :
    stripProfile left width cut slope count old x =
      old (meshPoint left width j) +
        cellProfile width cut slope
          (old (meshPoint left width (j + 1)) - old (meshPoint left width j))
          (x - meshPoint left width j) := by
  let grid := meshPoint left width
  let coeff := fun i => catchUpSlope width cut slope (old (grid (i + 1)) - old (grid i)) - slope
  let term := fun i => coeff i * clippedRamp (width - cut) (x - (grid i + cut))
  have hlen : 0 ≤ width - cut := sub_nonneg.mpr hcut.le
  have hmono : Monotone grid := meshPoint_mono (hcut₀.trans hcut.le)
  have htruncate : (∑ i ∈ Finset.range (j + 1), term i) =
      ∑ i ∈ Finset.range count, term i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hin
    simp only [Finset.mem_range] at hi hin
    have hgrid := hmono (show j + 1 ≤ i by omega)
    have hle : x - (grid i + cut) ≤ 0 := by linarith
    simp [term, clippedRamp_of_nonpos hle]
  let offset := fun i => old (grid i) - slope * (grid i - left)
  have htelescoping : (∑ i ∈ Finset.range j, term i) = offset j - offset 0 := by
    calc
      _ = ∑ i ∈ Finset.range j, (offset (i + 1) - offset i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hgrid := (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).trans hx₁
        have hstep : grid (i + 1) = grid i + width := meshPoint_succ _ _ _
        have hfull : width - cut ≤ x - (grid i + cut) := by linarith
        have hr := cellProfile_right
          (slope := slope) (rise := old (grid (i + 1)) - old (grid i)) hcut
        rw [cellProfile, max_eq_left hlen] at hr
        dsimp [term, coeff, offset]
        rw [clippedRamp_of_length_le hlen hfull]
        rw [hstep] at hr ⊢
        linarith [congrArg (fun t : ℝ => slope * t) hstep]
      _ = _ := Finset.sum_range_sub offset j
  have hcurrent : x - (grid j + cut) ≤ width - cut := by
    have hstep : grid (j + 1) = grid j + width := meshPoint_succ _ _ _
    change x ≤ grid (j + 1) at hx₂
    linarith
  have hzero : grid 0 = left := by simp [grid, meshPoint]
  change old left + slope * (x - left) + ∑ i ∈ Finset.range count, term i =
    old (grid j) + cellProfile width cut slope (old (grid (j + 1)) - old (grid j)) (x - grid j)
  rw [← htruncate, Finset.sum_range_succ, htelescoping]
  dsimp [offset, term, coeff, clippedRamp, cellProfile]
  rw [hzero, min_eq_left hcurrent]
  have hdifference : x - (grid j + cut) = x - grid j - cut := by ring
  rw [hdifference]
  ring


theorem stripProfile_cell_endpoints {left width cut slope : ℝ} {count j : ℕ}
    {old : ℝ → ℝ} (hcut₀ : 0 ≤ cut) (hcut : cut < width) (hj : j < count) :
    stripProfile left width cut slope count old (meshPoint left width j) =
      old (meshPoint left width j) ∧
    stripProfile left width cut slope count old (meshPoint left width (j + 1)) =
      old (meshPoint left width (j + 1)) := by
  have hwidth : 0 ≤ width := hcut₀.trans hcut.le
  have hstep := meshPoint_succ left width j
  have hle := meshPoint_mono (left := left) hwidth (Nat.le_succ j)
  constructor
  · rw [stripProfile_eq_cellProfile hcut₀ hcut hj le_rfl hle, sub_self,
      cellProfile_left hcut₀, add_zero]
  · rw [stripProfile_eq_cellProfile hcut₀ hcut hj hle le_rfl]
    have hdiff : meshPoint left width (j + 1) - meshPoint left width j = width := by
      linarith
    rw [hdiff, cellProfile_right hcut]
    ring

/-- Both old and new heights stay between the old grid endpoint values.
The resulting bound depends only on the oscillation on that cell. -/
theorem stripProfile_cell_error {left width cut slope : ℝ} {count j : ℕ}
    {old : ℝ → ℝ} {x : ℝ} (hcut₀ : 0 ≤ cut) (hcut : cut < width) (hslope : 0 ≤ slope)
    (hrise : ∀ i < count, slope * width ≤
      old (meshPoint left width (i + 1)) - old (meshPoint left width i))
    (hj : j < count) (hx₁ : meshPoint left width j ≤ x)
    (hx₂ : x ≤ meshPoint left width (j + 1))
    (hold₁ : old (meshPoint left width j) ≤ old x)
    (hold₂ : old x ≤ old (meshPoint left width (j + 1))) :
    |stripProfile left width cut slope count old x - old x| ≤
      old (meshPoint left width (j + 1)) - old (meshPoint left width j) := by
  obtain ⟨hleft, hright⟩ := stripProfile_cell_endpoints (old := old)
    (slope := slope) hcut₀ hcut hj
  have hlo := stripProfile_lower_slope hcut hrise hx₁
  have hhi := stripProfile_lower_slope hcut hrise hx₂
  rw [hleft] at hlo
  rw [hright] at hhi
  exact abs_le.mpr ⟨by linarith [mul_nonneg hslope (sub_nonneg.mpr hx₁)],
    by linarith [mul_nonneg hslope (sub_nonneg.mpr hx₂)]⟩

end

end GlobeFlattening
