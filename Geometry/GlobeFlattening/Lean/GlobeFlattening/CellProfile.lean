import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Longitude profile on one refinement interval

The interval is translated to start at zero. The first segment has the slope
chosen for the tile. The second segment restores the old right endpoint.
-/

namespace GlobeFlattening

noncomputable section

/-- The rise per unit length on the short second segment. -/
def catchUpSlope (width cut slope rise : ℝ) : ℝ :=
  (rise - slope * cut) / (width - cut)

/-- Height above the old left endpoint on a single grid interval. -/
def cellProfile (width cut slope rise x : ℝ) : ℝ :=
  slope * x + (catchUpSlope width cut slope rise - slope) * max (x - cut) 0

theorem cellProfile_of_le_cut {width cut slope rise x : ℝ} (hx : x ≤ cut) :
    cellProfile width cut slope rise x = slope * x := by
  simp [cellProfile, max_eq_right (sub_nonpos.mpr hx)]

theorem cellProfile_left {width cut slope rise : ℝ} (hcut : 0 ≤ cut) :
    cellProfile width cut slope rise 0 = 0 := by
  rw [cellProfile_of_le_cut hcut, mul_zero]

theorem cellProfile_right {width cut slope rise : ℝ} (hcut : cut < width) :
    cellProfile width cut slope rise width = rise := by
  have hgap : width - cut ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcut)
  rw [cellProfile, max_eq_left (sub_nonneg.mpr hcut.le), catchUpSlope]
  field_simp [hgap]; ring

theorem le_catchUpSlope {width cut slope rise : ℝ} (hcut : cut < width)
    (hrise : slope * width ≤ rise) : slope ≤ catchUpSlope width cut slope rise := by
  rw [catchUpSlope, le_div_iff₀ (sub_pos.mpr hcut)]
  nlinarith

/-- The full two-segment profile has the same lower slope as its first segment. -/
theorem cellProfile_lower_slope {width cut slope rise x₁ x₂ : ℝ}
    (hcut : cut < width) (hrise : slope * width ≤ rise) (hx : x₁ ≤ x₂) :
    slope * (x₂ - x₁) ≤
      cellProfile width cut slope rise x₂ - cellProfile width cut slope rise x₁ := by
  have hcoeff := le_catchUpSlope hcut hrise
  have hmax : max (x₁ - cut) 0 ≤ max (x₂ - cut) 0 :=
    max_le_max (sub_le_sub_right hx cut) le_rfl
  have hmul := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hcoeff)
  unfold cellProfile
  linarith

/-- If the old profile is affine with slope `a` on the entire interval,
the error is at most the drop in slope times the length of the first segment. -/
theorem cellProfile_affine_error {width cut slope a x : ℝ}
    (hcut0 : 0 ≤ cut) (hcut : cut < width) (hslopes : slope ≤ a)
    (hx0 : 0 ≤ x) (hxw : x ≤ width) :
    |cellProfile width cut slope (a * width) x - a * x| ≤ (a - slope) * cut := by
  have hprod : 0 ≤ (a - slope) * cut := mul_nonneg (sub_nonneg.mpr hslopes) hcut0
  have ha : 0 ≤ a - slope := sub_nonneg.mpr hslopes
  by_cases hxc : x ≤ cut
  · rw [cellProfile_of_le_cut hxc, abs_of_nonpos (by nlinarith [mul_nonneg ha hx0])]
    calc
      -(slope * x - a * x) = (a - slope) * x := by ring
      _ ≤ (a - slope) * cut := mul_le_mul_of_nonneg_left hxc ha
  · have hc : cut ≤ x := le_of_not_ge hxc
    have hwidth : 0 < width - cut := sub_pos.mpr hcut
    have hformula :
        cellProfile width cut slope (a * width) x - a * x =
          -((a - slope) * cut * ((width - x) / (width - cut))) := by
      rw [cellProfile, max_eq_left (sub_nonneg.mpr hc), catchUpSlope]
      field_simp [hwidth.ne']; ring
    have hratio0 : 0 ≤ (width - x) / (width - cut) :=
      div_nonneg (sub_nonneg.mpr hxw) hwidth.le
    have hratio1 : (width - x) / (width - cut) ≤ 1 := by
      rw [div_le_iff₀ hwidth, one_mul]
      linarith
    rw [hformula, abs_neg, abs_of_nonneg (mul_nonneg hprod hratio0)]
    simpa using mul_le_mul_of_nonneg_left hratio1 hprod

end

end GlobeFlattening
