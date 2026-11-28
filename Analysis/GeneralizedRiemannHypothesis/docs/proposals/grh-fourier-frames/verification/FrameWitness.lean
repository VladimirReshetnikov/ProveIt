import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.Ring

/-! Local estimates for a member of a punctured Fourier frame. These are valid
over any nonarchimedean normed field, independently of its residue characteristic. -/

namespace VacuumFrame.Local

variable {F : Type*} [NormedField F]

private theorem scaled_fraction_norm {c P D z : F} (hc : ‖c‖ = 1) (hP : P ≠ 0)
    (hslope : ‖D‖ * ‖z - 1‖ = ‖P‖) :
    ‖D * ((c / P) * (z - 1))‖ = 1 := by
  rw [norm_mul, norm_mul, norm_div, hc]
  calc
    ‖D‖ * (1 / ‖P‖ * ‖z - 1‖) = (‖D‖ * ‖z - 1‖) / ‖P‖ := by ring
    _ = 1 := by rw [hslope, div_self (norm_ne_zero_iff.mpr hP)]

variable [IsUltrametricDist F]

/-- At a place dividing the different, the second summand supplies the unit. -/
theorem unit_witness {T z c P D : F} (hT : ‖T‖ ≤ 1) (hz : ‖z‖ = 1)
    (hc : ‖c‖ = 1) (hP : P ≠ 0) (hD : ‖D‖ < 1)
    (hslope : ‖D‖ * ‖z - 1‖ = ‖P‖) :
    ‖D‖ * ‖T * z + (c / P) * (z - 1)‖ = 1 := by
  have hsmall : ‖D * (T * z)‖ < 1 := by
    rw [norm_mul, norm_mul, hz, mul_one]
    exact (mul_le_of_le_one_right (norm_nonneg _) hT).trans_lt hD
  have hunit := scaled_fraction_norm hc hP hslope
  have hlt : ‖D * (T * z)‖ < ‖D * ((c / P) * (z - 1))‖ := hunit ▸ hsmall
  rw [← norm_mul, mul_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne,
    max_eq_right hlt.le, hunit]

/-- On the same side, norm at most one for the scaled vector also covers the
case where the different is a unit and the two summands might cancel. -/
theorem scaled_integral {T z c P D : F} (hT : ‖T‖ ≤ 1) (hz : ‖z‖ = 1)
    (hc : ‖c‖ = 1) (hP : P ≠ 0) (hD : ‖D‖ ≤ 1)
    (hslope : ‖D‖ * ‖z - 1‖ = ‖P‖) :
    ‖D‖ * ‖T * z + (c / P) * (z - 1)‖ ≤ 1 := by
  rw [← norm_mul, mul_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_mul, hz, mul_one]
    exact (mul_le_of_le_one_right (norm_nonneg _) hT).trans hD
  · exact (scaled_fraction_norm hc hP hslope).le

/-- At the other places the unscaled vector is integral if its scalar
coefficient c/P is integral. -/
theorem integral_of_integral_coefficient {T z c P : F} (hT : ‖T‖ ≤ 1) (hz : ‖z‖ = 1)
    (hcoeff : ‖c / P‖ ≤ 1) :
    ‖T * z + (c / P) * (z - 1)‖ ≤ 1 := by
  have hdiff : ‖z - 1‖ ≤ 1 := by
    simpa [sub_eq_add_neg, hz] using (IsUltrametricDist.norm_add_le_max z (-1))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · simpa [norm_mul, hz] using hT
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hdiff).trans hcoeff

end VacuumFrame.Local

#print axioms VacuumFrame.Local.unit_witness
#print axioms VacuumFrame.Local.scaled_integral
#print axioms VacuumFrame.Local.integral_of_integral_coefficient
