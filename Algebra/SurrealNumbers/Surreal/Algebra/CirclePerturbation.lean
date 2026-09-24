import Mathlib.Tactic

/-!
# Algebraic bounds for perturbing a circle coordinate

These ordered-field and rational identities are prerequisites for
`trigonometry:thm:conditioned`. They control the endpoint margin and the
reciprocal sum of the original and perturbed positive circle heights.
-/

namespace Surreal.CirclePerturbation

variable {F : Type*} [Field F]

/-- The explicit second-order remainder in the reciprocal height sum. -/
def heightRemainder (c s u w : F) : F :=
  c * (2 * c + s ^ 2 * u) * w ^ 2 * (w + 1 / 2) + s ^ 2 * w ^ 2

/-- The reciprocal height sum has a quadratic remainder given by a rational expression. -/
theorem reciprocal_height_expansion (c s u r : F) (hr : r ^ 2 = 1 - 2 * c * u - s ^ 2 * u ^ 2)
    (hne : 1 + r ≠ 0) [CharZero F] :
    2 * (1 + r)⁻¹ = 1 + c / 2 * u + u ^ 2 * heightRemainder c s u (1 + r)⁻¹ := by
  have he : 2 * (1 + r)⁻¹ - 1 = u * (2 * c + s ^ 2 * u) * ((1 + r)⁻¹) ^ 2 := by
    field_simp
    linear_combination -hr
  unfold heightRemainder
  linear_combination (1 + c * u * ((1 + r)⁻¹ + 1 / 2)) * he

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- A positive circle height places its horizontal coordinate in the open interval. -/
theorem coordinate_mem_Ioo (c s : F) (hs : 0 < s) (hcircle : c ^ 2 + s ^ 2 = 1) :
    c ∈ Set.Ioo (-1) 1 := by
  have hsp := sq_pos_of_pos hs
  constructor <;> nlinarith

/-- The distance to the nearer endpoint is the squared height divided by `1+|c|`. -/
theorem endpoint_margin (c s : F) (hcircle : c ^ 2 + s ^ 2 = 1) :
    1 - |c| = s ^ 2 / (1 + |c|) := by
  have hn : 1 + |c| ≠ 0 := (by positivity : 0 < 1 + |c|).ne'
  apply (eq_div_iff hn).mpr
  nlinarith [sq_abs c]

/-- A perturbation smaller than half the squared height stays strictly between the endpoints. -/
theorem perturbed_mem_Ioo (c s e : F) (hs : 0 < s) (hcircle : c ^ 2 + s ^ 2 = 1)
    (he : |e / s ^ 2| < 1 / 2) : c + e ∈ Set.Ioo (-1) 1 := by
  have hsp : 0 < s ^ 2 := sq_pos_of_pos hs
  rw [abs_div, abs_of_pos hsp, div_lt_iff₀ hsp] at he
  have hm : s ^ 2 / 2 ≤ 1 - |c| := by
    nlinarith [sq_abs c, sq_nonneg (1 - |c|)]
  apply abs_lt.mp
  calc
    |c + e| ≤ |c| + |e| := abs_add_le _ _
    _ < 1 := by linarith

end Surreal.CirclePerturbation
