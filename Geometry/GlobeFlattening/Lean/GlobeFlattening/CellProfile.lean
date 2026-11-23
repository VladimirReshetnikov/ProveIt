import GlobeFlattening.RampProfile

/-!
# Longitude profile on one refinement interval

The interval starts at zero. The affine part has the prescribed slope.
The ramp over the short second segment restores the old right endpoint.
-/

namespace GlobeFlattening

noncomputable section

/-- Height above the old left endpoint on a single grid interval. -/
def cellProfile (width cut slope rise x : ℝ) : ℝ :=
  slope * x + rampWeight cut (width - cut) x * (rise - slope * width)

theorem cellProfile_of_le_cut {width cut slope rise x : ℝ} (hx : x ≤ cut) :
    cellProfile width cut slope rise x = slope * x := by
  simp [cellProfile, rampWeight_eq_zero hx]

theorem cellProfile_left {width cut slope rise : ℝ} (hcut : 0 ≤ cut) :
    cellProfile width cut slope rise 0 = 0 := by
  rw [cellProfile_of_le_cut hcut, mul_zero]

theorem cellProfile_right {width cut slope rise : ℝ} (hcut : cut < width) :
    cellProfile width cut slope rise width = rise := by
  rw [cellProfile, rampWeight_eq_one (sub_pos.mpr hcut) (by linarith), one_mul, add_sub_cancel]

/-- If the old profile is affine with slope `a` on the entire interval,
the error is at most the drop in slope times the length of the first segment. -/
theorem cellProfile_affine_error {width cut slope a x : ℝ}
    (hcut₀ : 0 ≤ cut) (hcut : cut < width) (hslopes : slope ≤ a)
    (hx₀ : 0 ≤ x) (hxw : x ≤ width) :
    |cellProfile width cut slope (a * width) x - a * x| ≤ (a - slope) * cut := by
  let t := rampWeight cut (width - cut) x
  have hfactor : cellProfile width cut slope (a * width) x - a * x =
      (a - slope) * (width * t - x) := by
    unfold cellProfile t
    ring
  rw [hfactor, abs_mul, abs_of_nonneg (sub_nonneg.mpr hslopes)]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hslopes)
  by_cases hx : x ≤ cut
  · rw [show t = 0 from rampWeight_eq_zero hx, mul_zero, zero_sub, abs_neg, abs_of_nonneg hx₀]
    exact hx
  · have hw := sub_pos.mpr hcut
    have ht := rampWeight_bounds (start := cut) (y := x) hw
    have hweight : t * (width - cut) = x - cut := by
      unfold t rampWeight clippedRamp
      rw [min_eq_left (sub_le_sub_right hxw cut),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge hx)), div_mul_cancel₀ _ hw.ne']
    have hshape : width * t - x = -(cut * (1 - t)) := by linarith only [hweight]
    rw [hshape, abs_neg, abs_of_nonneg (mul_nonneg hcut₀ (sub_nonneg.mpr ht.2))]
    nlinarith only [mul_nonneg hcut₀ ht.1]

end

end GlobeFlattening
