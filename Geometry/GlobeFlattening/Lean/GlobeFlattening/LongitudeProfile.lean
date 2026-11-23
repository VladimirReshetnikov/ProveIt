import GlobeFlattening.CellProfile

/-!
# Continuous longitude profiles across a row of cells

Subtract the prescribed affine slope from the old heights at the grid points.
The short segments interpolate the resulting offsets with the same ramp sum
used by the latitude profiles.
-/

open scoped BigOperators

namespace GlobeFlattening

noncomputable section

def meshPoint (left width : ℝ) (j : ℕ) : ℝ := left + j * width

theorem meshPoint_succ (left width : ℝ) (j : ℕ) :
    meshPoint left width (j + 1) = meshPoint left width j + width := by
  unfold meshPoint
  push_cast
  ring

theorem meshPoint_mono {left width : ℝ} (hwidth : 0 ≤ width) :
    Monotone (meshPoint left width) :=
  fun _ _ h => add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) hwidth)

private def stripOffset (left width slope : ℝ) (old : ℝ → ℝ) (j : ℕ) : ℝ :=
  old (meshPoint left width j) - slope * (meshPoint left width j - left)

private theorem stripOffset_rise (left width slope : ℝ) (old : ℝ → ℝ) (j : ℕ) :
    stripOffset left width slope old (j + 1) - stripOffset left width slope old j =
      old (meshPoint left width (j + 1)) - old (meshPoint left width j) - slope * width := by
  unfold stripOffset
  rw [meshPoint_succ]
  ring

def stripProfile (left width cut slope : ℝ) (count : ℕ) (old : ℝ → ℝ) (x : ℝ) : ℝ :=
  slope * (x - left) + rampProfile count (stripOffset left width slope old)
    (fun j => rampWeight (meshPoint left width j + cut) (width - cut) x)

theorem continuous_stripProfile (left width cut slope : ℝ)
    (count : ℕ) (old : ℝ → ℝ) :
    Continuous (stripProfile left width cut slope count old) := by
  unfold stripProfile rampProfile rampWeight clippedRamp
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
  unfold stripProfile
  have h := rampProfile_mono_weight (count := count) (height := stripOffset left width slope old)
    (w₁ := fun j => rampWeight (meshPoint left width j + cut) (width - cut) x₁)
    (w₂ := fun j => rampWeight (meshPoint left width j + cut) (width - cut) x₂)
    (fun j hj => sub_nonneg.mp (by rw [stripOffset_rise]; exact sub_nonneg.mpr (hrise j hj)))
    (fun _ _ => rampWeight_mono _ _ (sub_nonneg.mpr hcut.le) hx)
  linarith only [h]

/-- On a closed mesh cell the strip is the translated single-cell profile. -/
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
  have hw := sub_pos.mpr hcut
  have hmono := meshPoint_mono (left := left) (hcut₀.trans hcut.le)
  have h₁ : ∀ i < j, rampWeight (grid i + cut) (width - cut) x = 1 := by
    intro i hi
    apply rampWeight_eq_one hw
    calc
      grid i + cut + (width - cut) = grid i + width := by ring
      _ = grid (i + 1) := (meshPoint_succ _ _ _).symm
      _ ≤ x := (hmono (Nat.succ_le_of_lt hi)).trans hx₁
  have h₂ : ∀ i < count, j < i → rampWeight (grid i + cut) (width - cut) x = 0 := by
    intro i _ hi
    exact rampWeight_eq_zero
      ((hx₂.trans (hmono (Nat.succ_le_of_lt hi))).trans (le_add_of_nonneg_right hcut₀))
  have hweight : rampWeight (grid j + cut) (width - cut) x =
      rampWeight cut (width - cut) (x - grid j) := by
    unfold rampWeight
    rw [sub_sub]
  unfold stripProfile
  rw [rampProfile_at_layer hj h₁ h₂, stripOffset_rise, hweight]
  unfold stripOffset cellProfile
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

/-- The new height stays between the old endpoint heights of its cell. -/
theorem stripProfile_cell_bounds {left width cut slope : ℝ} {count j : ℕ}
    {old : ℝ → ℝ} {x : ℝ} (hcut₀ : 0 ≤ cut) (hcut : cut < width) (hslope : 0 ≤ slope)
    (hrise : ∀ i < count, slope * width ≤
      old (meshPoint left width (i + 1)) - old (meshPoint left width i))
    (hj : j < count) (hx₁ : meshPoint left width j ≤ x)
    (hx₂ : x ≤ meshPoint left width (j + 1)) :
    stripProfile left width cut slope count old x ∈
      Set.Icc (old (meshPoint left width j)) (old (meshPoint left width (j + 1))) := by
  obtain ⟨hleft, hright⟩ := stripProfile_cell_endpoints (old := old)
    (slope := slope) hcut₀ hcut hj
  have hlo := stripProfile_lower_slope hcut hrise hx₁
  have hhi := stripProfile_lower_slope hcut hrise hx₂
  rw [hleft] at hlo
  rw [hright] at hhi
  exact ⟨sub_nonneg.mp ((mul_nonneg hslope (sub_nonneg.mpr hx₁)).trans hlo),
    sub_nonneg.mp ((mul_nonneg hslope (sub_nonneg.mpr hx₂)).trans hhi)⟩

end

end GlobeFlattening
