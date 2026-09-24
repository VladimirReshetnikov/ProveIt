import Surreal.Algebra.Geometry
import Mathlib.Analysis.Convex.Segment

/-!
# Orthogonal projection and field-valued distance to a line

Projection onto a nonzero direction is defined by its dot-product
coordinate. Its distance is the absolute determinant divided by the
direction's modulus, and the Pythagorean identity makes it the unique
nearest point. These constructions supply the contact-point geometry for
the incircle in `trigonometry:thm:heron`; all distances remain in the
ordered base field, including its infinite and infinitesimal scales.
-/

namespace Surreal.Complexify

section Field

variable {F : Type*} [Field F]

/-- The scalar coordinate of the perpendicular foot on the line through `p` along `v`. -/
def lineProjectionParameter (p v x : Complexify F) : F := dot v (x - p) / normSq v

/-- Orthogonal projection onto the line through `p` with direction `v`. -/
def lineProjection (p v x : Complexify F) : Complexify F :=
  p + lineProjectionParameter p v x • v

/-- The projection is on its defining affine line. -/
theorem lineProjection_on_line (p v x : Complexify F) :
    ∃ t : F, lineProjection p v x = p + t • v :=
  ⟨lineProjectionParameter p v x, rfl⟩

/-- The dot product of a residual along a parameterized line. -/
theorem dot_sub_linePoint (p v x : Complexify F) (t : F) :
    dot v (x - (p + t • v)) = dot v (x - p) - t * normSq v := by
  simp only [dot_def, normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- Moving along a line preserves its determinant against the line direction. -/
theorem cross_sub_linePoint (p v x : Complexify F) (t : F) :
    cross v (x - (p + t • v)) = cross v (x - p) := by
  simp only [cross_def, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

end Field

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The displacement from a point to its foot is perpendicular to the line. -/
theorem dot_sub_lineProjection (p v x : Complexify F) (hv : v ≠ 0) :
    dot v (x - lineProjection p v x) = 0 := by
  rw [lineProjection, dot_sub_linePoint, lineProjectionParameter,
    div_mul_cancel₀ _ (normSq_pos hv).ne', sub_self]

/-- Perpendicularity characterizes the projection parameter uniquely. -/
theorem lineProjectionParameter_eq_of_perpendicular (p v x : Complexify F) (hv : v ≠ 0)
    (t : F) (ht : dot v (x - (p + t • v)) = 0) : lineProjectionParameter p v x = t := by
  rw [dot_sub_linePoint] at ht
  apply (div_eq_iff (normSq_pos hv).ne').mpr
  exact sub_eq_zero.mp ht

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The projection residual retains the determinant of the original displacement. -/
theorem cross_sub_lineProjection (p v x : Complexify F) :
    cross v (x - lineProjection p v x) = cross v (x - p) :=
  cross_sub_linePoint p v x _

/-- Squared-distance decomposition along the entire line, without a restriction on the parameter. -/
theorem normSq_sub_linePoint (p v x : Complexify F) (hv : v ≠ 0) (t : F) :
    normSq (x - (p + t • v)) = normSq (x - lineProjection p v x) +
      (t - lineProjectionParameter p v x) ^ 2 * normSq v := by
  have he : x - (p + t • v) = (x - lineProjection p v x) -
      (t - lineProjectionParameter p v x) • v := by
    simp only [lineProjection, sub_smul]
    abel
  rw [he, normSq_sub, normSq_smul]
  have hd : dot (x - lineProjection p v x) ((t - lineProjectionParameter p v x) • v) = 0 := by
    have hp := dot_sub_lineProjection p v x hv
    rw [dot_comm] at hp
    have hs : dot (x - lineProjection p v x) ((t - lineProjectionParameter p v x) • v) =
        (t - lineProjectionParameter p v x) * dot (x - lineProjection p v x) v := by
      simp only [dot_def, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
      ring
    rw [hs, hp, mul_zero]
  rw [hd, mul_zero, sub_zero]

/-- A projection whose parameter lies strictly between zero and one is inside the side segment. -/
theorem lineProjection_mem_openSegment (p q x : Complexify F)
    (ht : lineProjectionParameter p (q - p) x ∈ Set.Ioo (0 : F) 1) :
    lineProjection p (q - p) x ∈ openSegment F p q := by
  let t := lineProjectionParameter p (q - p) x
  refine ⟨1 - t, t, sub_pos.mpr ht.2, ht.1, by ring, ?_⟩
  change (1 - t) • p + t • q = p + t • (q - p)
  simp only [sub_smul, smul_sub, one_smul]
  abel

variable [HasNonnegSquareRoots F]

/-- Distance to the actual perpendicular foot, with values in the ordered base field. -/
noncomputable def lineDistance (p v x : Complexify F) : F := modulus (x - lineProjection p v x)

theorem lineDistance_nonneg (p v x : Complexify F) : 0 ≤ lineDistance p v x :=
  modulus_nonneg _

/-- The determinant formula is the length of the perpendicular segment, not a formal radius. -/
theorem lineDistance_eq_cross_div (p v x : Complexify F) (hv : v ≠ 0) :
    lineDistance p v x = |cross v (x - p)| / modulus v := by
  apply modulus_eq_of_nonneg_sq
  · exact div_nonneg (abs_nonneg _) (modulus_nonneg v)
  · rw [div_pow, sq_abs, modulus_sq]
    apply (div_eq_iff (normSq_pos hv).ne').mpr
    have he := dot_sq_add_cross_sq v (x - lineProjection p v x)
    rw [dot_sub_lineProjection p v x hv, zero_pow (by norm_num : 2 ≠ 0), zero_add,
      cross_sub_lineProjection] at he
    exact he.trans (mul_comm _ _)

/-- The perpendicular foot minimizes every distance to the line. -/
theorem lineDistance_le_linePoint (p v x : Complexify F) (hv : v ≠ 0) (t : F) :
    lineDistance p v x ≤ modulus (x - (p + t • v)) := by
  apply (sq_le_sq₀ (lineDistance_nonneg p v x) (modulus_nonneg _)).mp
  change modulus (x - lineProjection p v x) ^ 2 ≤ _
  rw [modulus_sq, modulus_sq, normSq_sub_linePoint p v x hv t]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (normSq_nonneg _))

/-- Equality in the minimum-distance bound uniquely determines the foot's line parameter. -/
theorem lineDistance_eq_linePoint_iff (p v x : Complexify F) (hv : v ≠ 0) (t : F) :
    lineDistance p v x = modulus (x - (p + t • v)) ↔
      t = lineProjectionParameter p v x := by
  constructor
  · intro he
    have hs := congrArg (fun r : F => r ^ 2) he
    change modulus (x - lineProjection p v x) ^ 2 = _ at hs
    rw [modulus_sq, modulus_sq, normSq_sub_linePoint p v x hv t] at hs
    have hz : (t - lineProjectionParameter p v x) ^ 2 * normSq v = 0 := by
      linarith only [hs]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right (normSq_pos hv).ne'))
  · rintro rfl
    rfl

/-- The circle at the perpendicular distance meets the line at exactly its perpendicular foot. -/
theorem existsUnique_line_contact (p v x : Complexify F) (hv : v ≠ 0) :
    ∃! y : Complexify F, (∃ t : F, y = p + t • v) ∧
      modulus (x - y) = lineDistance p v x := by
  refine ⟨lineProjection p v x, ⟨lineProjection_on_line p v x, rfl⟩, ?_⟩
  rintro y ⟨⟨t, rfl⟩, he⟩
  rw [(lineDistance_eq_linePoint_iff p v x hv t).mp he.symm]
  rfl

end OrderedField
end Surreal.Complexify
