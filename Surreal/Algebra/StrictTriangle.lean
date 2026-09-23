import Surreal.Algebra.Geometry

/-!
# Strict triangle inequalities from noncollinearity

The equality case of the field-valued triangle inequality forces the
determinant to vanish. This supplies the necessity clause of
`trigonometry:thm:sss` without an Archimedean hypothesis.
-/

namespace Surreal.Complexify

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [HasNonnegSquareRoots F]

/-- Independent vectors have strict inequality in the field-valued norm triangle law. -/
theorem modulus_add_lt_of_cross_ne_zero (z w : Complexify F) (h : cross z w ≠ 0) :
    modulus (z + w) < modulus z + modulus w := by
  apply lt_of_le_of_ne (modulus_add_le z w)
  intro he
  have hd := (modulus_add_eq_iff_dot z w).mp he
  have hg := dot_sq_add_cross_sq z w
  rw [hd, mul_pow, modulus_sq, modulus_sq] at hg
  exact h (sq_eq_zero_iff.mp (by linarith only [hg]))

/-- The distance between independent vectors is strictly smaller than their total lengths. -/
theorem modulus_sub_lt_of_cross_ne_zero (z w : Complexify F) (h : cross z w ≠ 0) :
    modulus (z - w) < modulus z + modulus w := by
  have hc : cross z (-w) = -cross z w := by
    simp only [cross_def, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]
    ring
  have he := modulus_add_lt_of_cross_ne_zero z (-w) (by rwa [hc, neg_ne_zero])
  simpa only [← sub_eq_add_neg, modulus_neg] using he

end Surreal.Complexify
