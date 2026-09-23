import Surreal.Algebra.Geometry

/-!
# Circumcircles over an ordered field with square roots

The perpendicular-bisector equations have a unique solution for every
noncollinear triangle. Its actual field-valued radius is the product of
the three side lengths divided by twice the absolute determinant. These
are the circumcircle clauses of `trigonometry:thm:trianglelaws` and
`trigonometry:eq:trianglelaws`, without a finiteness or compactness assumption.
-/

namespace Surreal.Complexify

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The center of the circle through `0`, `z`, and `w`, given by the two linear equations. -/
def circumcenter (z w : Complexify F) : Complexify F :=
  ⟨(normSq z * w.im - normSq w * z.im) / (2 * cross z w),
    (z.re * normSq w - w.re * normSq z) / (2 * cross z w)⟩

/-- The center satisfies the first perpendicular-bisector equation. -/
theorem circumcenter_dot_left (z w : Complexify F) (h : cross z w ≠ 0) :
    2 * dot (circumcenter z w) z = normSq z := by
  simp only [dot_def, circumcenter]
  field_simp [h]
  simp only [cross_def, normSq]
  ring

/-- The center satisfies the second perpendicular-bisector equation. -/
theorem circumcenter_dot_right (z w : Complexify F) (h : cross z w ≠ 0) :
    2 * dot (circumcenter z w) w = normSq w := by
  simp only [dot_def, circumcenter]
  field_simp [h]
  simp only [cross_def, normSq]
  ring

/-- Dot products against two independent vectors determine a vector uniquely. -/
theorem eq_of_dot_eq_of_cross_ne_zero (z w : Complexify F) (h : cross z w ≠ 0)
    {p q : Complexify F} (hz : dot p z = dot q z) (hw : dot p w = dot q w) : p = q := by
  simp only [dot_def] at hz hw
  apply QuadraticAlgebra.ext
  · apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show cross z w * (p.re - q.re) = 0 by
      rw [cross_def]
      linear_combination w.im * hz - z.im * hw)).resolve_left h
  · apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show cross z w * (p.im - q.im) = 0 by
      rw [cross_def]
      linear_combination z.re * hw - w.re * hz)).resolve_left h

/-- Direct expansion of the center gives its squared circumradius. -/
theorem normSq_circumcenter (z w : Complexify F) (h : cross z w ≠ 0) :
    normSq (circumcenter z w) = normSq (z - w) * normSq z * normSq w / (4 * cross z w ^ 2) := by
  have hd : z.re * w.im - z.im * w.re ≠ 0 := by simpa only [cross_def] using h
  simp only [circumcenter, normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, cross_def]
  field_simp [hd]
  ring

variable [HasNonnegSquareRoots F]

/-- Equality of distances from `0` and `z` is precisely a linear dot-product equation. -/
theorem modulus_sub_eq_modulus_iff_dot (p z : Complexify F) :
    modulus (p - z) = modulus p ↔ 2 * dot p z = normSq z := by
  constructor
  · intro h
    have hs := congrArg (fun r : F => r ^ 2) h
    rw [modulus_sq, modulus_sq, normSq_sub] at hs
    linarith only [hs]
  · intro h
    apply (sq_eq_sq₀ (modulus_nonneg _) (modulus_nonneg _)).mp
    rw [modulus_sq, modulus_sq, normSq_sub]
    linarith only [h]

/-- The explicit center has equal distances from all three vertices. -/
theorem circumcenter_equidistant (z w : Complexify F) (h : cross z w ≠ 0) :
    modulus (circumcenter z w - z) = modulus (circumcenter z w) ∧
      modulus (circumcenter z w - w) = modulus (circumcenter z w) :=
  ⟨(modulus_sub_eq_modulus_iff_dot _ _).mpr (circumcenter_dot_left z w h),
    (modulus_sub_eq_modulus_iff_dot _ _).mpr (circumcenter_dot_right z w h)⟩

/-- Every center equidistant from the three vertices equals the explicit one. -/
theorem eq_circumcenter_of_equidistant (z w : Complexify F) (h : cross z w ≠ 0)
    (p : Complexify F) (hz : modulus (p - z) = modulus p)
    (hw : modulus (p - w) = modulus p) : p = circumcenter z w := by
  apply eq_of_dot_eq_of_cross_ne_zero z w h
  · have hp := (modulus_sub_eq_modulus_iff_dot p z).mp hz
    have hc := circumcenter_dot_left z w h
    linarith only [hp, hc]
  · have hp := (modulus_sub_eq_modulus_iff_dot p w).mp hw
    have hc := circumcenter_dot_right z w h
    linarith only [hp, hc]

/-- A noncollinear triangle has exactly one circumcenter. -/
theorem existsUnique_circumcenter (z w : Complexify F) (h : cross z w ≠ 0) :
    ∃! p : Complexify F, modulus (p - z) = modulus p ∧ modulus (p - w) = modulus p := by
  refine ⟨circumcenter z w, circumcenter_equidistant z w h, ?_⟩
  rintro p ⟨hpz, hpw⟩
  exact eq_circumcenter_of_equidistant z w h p hpz hpw

/-- The circumradius is the product of side lengths divided by twice the absolute determinant. -/
theorem modulus_circumcenter (z w : Complexify F) (h : cross z w ≠ 0) :
    modulus (circumcenter z w) =
      modulus (z - w) * modulus z * modulus w / (2 * |cross z w|) := by
  apply modulus_eq_of_nonneg_sq
  · exact div_nonneg
      (mul_nonneg (mul_nonneg (modulus_nonneg _) (modulus_nonneg _)) (modulus_nonneg _))
      (mul_nonneg (by norm_num) (abs_nonneg _))
  · simp only [div_pow, mul_pow, modulus_sq, sq_abs]
    rw [normSq_circumcenter z w h]
    norm_num

omit [HasNonnegSquareRoots F] in
/-- The center of a noncollinear triangle with one vertex zero is nonzero. -/
theorem circumcenter_ne_zero (z w : Complexify F) (h : cross z w ≠ 0) :
    circumcenter z w ≠ 0 := by
  intro hc
  have hd := circumcenter_dot_left z w h
  rw [hc] at hd
  have hz : z = 0 := (normSq_eq_zero_iff z).mp (by simpa [dot_def] using hd.symm)
  simp [hz, cross_def] at h

/-- The actual circumradius is strictly positive. -/
theorem modulus_circumcenter_pos (z w : Complexify F) (h : cross z w ≠ 0) :
    0 < modulus (circumcenter z w) := modulus_pos (circumcenter_ne_zero z w h)

/-- A noncollinear triangle has one circle with positive field-valued radius through its vertices. -/
theorem existsUnique_circumcircle (z w : Complexify F) (h : cross z w ≠ 0) :
    ∃! p : Complexify F × F, 0 < p.2 ∧ modulus p.1 = p.2 ∧
      modulus (p.1 - z) = p.2 ∧ modulus (p.1 - w) = p.2 := by
  obtain ⟨hz, hw⟩ := circumcenter_equidistant z w h
  refine ⟨(circumcenter z w, modulus (circumcenter z w)),
    ⟨modulus_circumcenter_pos z w h, rfl, hz, hw⟩, ?_⟩
  rintro ⟨p, r⟩ ⟨_, hr, hpz, hpw⟩
  have hc := eq_circumcenter_of_equidistant z w h p (hpz.trans hr.symm) (hpw.trans hr.symm)
  exact Prod.ext hc (hr.symm.trans (congrArg modulus hc))

end Surreal.Complexify
