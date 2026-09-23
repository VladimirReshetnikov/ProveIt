import Surreal.Surcomplex.TriangleHeron
import Mathlib.Analysis.Convex.Segment

/-!
# Internal bisectors of actual surcomplex triangles

The internal bisector construction in `trigonometry:thm:heron` and
`trigonometry:eq:bisector` works at arbitrary actual surreal scales.
Its weighted point lies strictly within the opposite side, divides that
side in the prescribed ratio, has the stated length, and makes two
actual angles each equal to half the original interior angle.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem cross_weighted_right (p q : SignSequence.{u}) (z w : Surcomplex.{u}) :
    Complexify.cross z (ofReal p * z + ofReal q * w) = q * Complexify.cross z w := by
  simp only [Complexify.cross_def, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    mul_re, mul_im, ofReal_re, ofReal_im]
  ring

private theorem cross_weighted_left (p q : SignSequence.{u}) (z w : Surcomplex.{u}) :
    Complexify.cross (ofReal p * z + ofReal q * w) w = p * Complexify.cross z w := by
  simp only [Complexify.cross_def, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    mul_re, mul_im, ofReal_re, ofReal_im]
  ring

private theorem dot_weighted_right (p q : SignSequence.{u}) (z w : Surcomplex.{u}) :
    Complexify.dot z (ofReal p * z + ofReal q * w) =
      p * normSq z + q * Complexify.dot z w := by
  simp only [Complexify.dot_def, normSq_eq, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

private theorem dot_weighted_left (p q : SignSequence.{u}) (z w : Surcomplex.{u}) :
    Complexify.dot (ofReal p * z + ofReal q * w) w =
      p * Complexify.dot z w + q * normSq w := by
  simp only [Complexify.dot_def, normSq_eq, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

private theorem normSq_weighted (p q : SignSequence.{u}) (z w : Surcomplex.{u}) :
    normSq (ofReal p * z + ofReal q * w) =
      p ^ 2 * normSq z + q ^ 2 * normSq w + 2 * p * q * Complexify.dot z w := by
  simp only [Complexify.dot_def, normSq_eq, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

namespace Triangle

/-- The weighted point where the internal bisector from `A` meets `BC`. -/
def bisectorPoint (T : Triangle.{u}) : Surcomplex.{u} :=
  ofReal (T.sideB / (T.sideB + T.sideC)) * T.B +
    ofReal (T.sideC / (T.sideB + T.sideC)) * T.C

private theorem bisector_weights_sum (T : Triangle.{u}) :
    ofReal (T.sideB / (T.sideB + T.sideC)) +
      ofReal (T.sideC / (T.sideB + T.sideC)) = 1 := by
  rw [← map_add, ← add_div, div_self (add_pos T.sideB_pos T.sideC_pos).ne', map_one]

/-- The bisector point has the manuscript's barycentric expression. -/
theorem bisectorPoint_eq (T : Triangle.{u}) :
    T.bisectorPoint = (ofReal T.sideB * T.B + ofReal T.sideC * T.C) /
      ofReal (T.sideB + T.sideC) := by
  unfold bisectorPoint
  rw [map_div₀, map_div₀]
  ring

/-- Its side parameter is strictly between zero and one. -/
theorem bisector_parameter_mem (T : Triangle.{u}) :
    T.sideC / (T.sideB + T.sideC) ∈ Set.Ioo 0 1 := by
  have hs := add_pos T.sideB_pos T.sideC_pos
  exact ⟨div_pos T.sideC_pos hs, (div_lt_one hs).mpr (by linarith [T.sideB_pos])⟩

/-- The bisector meets the opposite side in Mathlib's open segment over the actual surreals. -/
theorem bisectorPoint_mem_openSegment (T : Triangle.{u}) :
    T.bisectorPoint ∈ openSegment SignSequence.{u} T.B T.C := by
  have hs := add_pos T.sideB_pos T.sideC_pos
  refine ⟨T.sideB / (T.sideB + T.sideC), T.sideC / (T.sideB + T.sideC),
    div_pos T.sideB_pos hs, div_pos T.sideC_pos hs, ?_, ?_⟩
  · rw [← add_div, div_self hs.ne']
  · rw [Algebra.smul_def, Algebra.smul_def]
    rfl

/-- The bisector point lies on the open side segment with its explicit parameter. -/
theorem bisectorPoint_eq_affine (T : Triangle.{u}) :
    T.bisectorPoint = T.B + ofReal (T.sideC / (T.sideB + T.sideC)) * (T.C - T.B) := by
  calc
    _ = (ofReal (T.sideB / (T.sideB + T.sideC)) +
        ofReal (T.sideC / (T.sideB + T.sideC))) * T.B +
        ofReal (T.sideC / (T.sideB + T.sideC)) * (T.C - T.B) := by
      unfold bisectorPoint
      ring
    _ = _ := by rw [bisector_weights_sum, one_mul]

theorem bisectorPoint_sub_A (T : Triangle.{u}) :
    T.bisectorPoint - T.A =
      ofReal (T.sideB / (T.sideB + T.sideC)) * (T.B - T.A) +
        ofReal (T.sideC / (T.sideB + T.sideC)) * (T.C - T.A) := by
  calc
    _ = T.bisectorPoint -
        (ofReal (T.sideB / (T.sideB + T.sideC)) +
          ofReal (T.sideC / (T.sideB + T.sideC))) * T.A := by
      rw [bisector_weights_sum, one_mul]
    _ = _ := by unfold bisectorPoint; ring

theorem B_sub_bisectorPoint (T : Triangle.{u}) :
    T.B - T.bisectorPoint =
      ofReal (T.sideC / (T.sideB + T.sideC)) * (T.B - T.C) := by
  rw [bisectorPoint_eq_affine]
  ring

theorem bisectorPoint_sub_C (T : Triangle.{u}) :
    T.bisectorPoint - T.C =
      ofReal (T.sideB / (T.sideB + T.sideC)) * (T.B - T.C) := by
  calc
    _ = T.bisectorPoint -
        (ofReal (T.sideB / (T.sideB + T.sideC)) +
          ofReal (T.sideC / (T.sideB + T.sideC))) * T.C := by
      rw [bisector_weights_sum, one_mul]
    _ = _ := by unfold bisectorPoint; ring

/-- The actual lengths cut by the internal bisector have ratio `c/b`. -/
theorem bisector_side_ratio (T : Triangle.{u}) :
    modulus (T.B - T.bisectorPoint) / modulus (T.bisectorPoint - T.C) =
      T.sideC / T.sideB := by
  have hs := add_pos T.sideB_pos T.sideC_pos
  rw [B_sub_bisectorPoint, bisectorPoint_sub_C, modulus_mul, modulus_mul,
    modulus_ofReal, modulus_ofReal, abs_of_pos (div_pos T.sideC_pos hs),
    abs_of_pos (div_pos T.sideB_pos hs)]
  change (T.sideC / (T.sideB + T.sideC) * T.sideA) /
    (T.sideB / (T.sideB + T.sideC) * T.sideA) = T.sideC / T.sideB
  field_simp [hs.ne', T.sideA_pos.ne', T.sideB_pos.ne']

/-- Both subtriangles cut by the bisector remain noncollinear. -/
theorem bisector_cross_left_ne_zero (T : Triangle.{u}) :
    Complexify.cross (T.B - T.A) (T.bisectorPoint - T.A) ≠ 0 := by
  rw [bisectorPoint_sub_A, cross_weighted_right]
  exact mul_ne_zero (div_pos T.sideC_pos (add_pos T.sideB_pos T.sideC_pos)).ne'
    T.noncollinear

theorem bisector_cross_right_ne_zero (T : Triangle.{u}) :
    Complexify.cross (T.bisectorPoint - T.A) (T.C - T.A) ≠ 0 := by
  rw [bisectorPoint_sub_A, cross_weighted_left]
  exact mul_ne_zero (div_pos T.sideB_pos (add_pos T.sideB_pos T.sideC_pos)).ne'
    T.noncollinear

private theorem dot_edges (T : Triangle.{u}) :
    Complexify.dot (T.B - T.A) (T.C - T.A) =
      T.sideB * T.sideC * finiteCos T.angleA := by
  have h := finiteCos_interiorAngle (T.B - T.A) (T.C - T.A) T.noncollinear
  rw [modulus_sub_comm T.B T.A] at h
  change finiteCos T.angleA = Complexify.dot (T.B - T.A) (T.C - T.A) /
    (T.sideC * T.sideB) at h
  rw [eq_div_iff (mul_ne_zero T.sideC_pos.ne' T.sideB_pos.ne')] at h
  linear_combination -h

private theorem cos_angleA_eq_half (T : Triangle.{u}) :
    finiteCos T.angleA = 2 * finiteCos (finiteHalf T.angleA) ^ 2 - 1 := by
  linarith only [finiteCos_finiteHalf_sq T.angleA]

/-- The internal bisector length in `trigonometry:eq:bisector`, in the actual surreal field. -/
theorem bisector_length (T : Triangle.{u}) :
    modulus (T.bisectorPoint - T.A) =
      2 * T.sideB * T.sideC / (T.sideB + T.sideC) * finiteCos (finiteHalf T.angleA) := by
  apply (sq_eq_sq₀ (modulus_nonneg _) (mul_nonneg
    (div_pos (mul_pos (mul_pos (by norm_num) T.sideB_pos) T.sideC_pos)
      (add_pos T.sideB_pos T.sideC_pos)).le T.cos_half_angleA_pos.le)).mp
  rw [modulus_sq, bisectorPoint_sub_A, normSq_weighted, ← modulus_sq (T.B - T.A),
    ← modulus_sq (T.C - T.A), modulus_sub_comm T.B T.A, dot_edges, cos_angleA_eq_half]
  change (T.sideB / (T.sideB + T.sideC)) ^ 2 * T.sideC ^ 2 +
      (T.sideC / (T.sideB + T.sideC)) ^ 2 * T.sideB ^ 2 +
      2 * (T.sideB / (T.sideB + T.sideC)) * (T.sideC / (T.sideB + T.sideC)) *
        (T.sideB * T.sideC * (2 * finiteCos (finiteHalf T.angleA) ^ 2 - 1)) = _
  field_simp [(add_pos T.sideB_pos T.sideC_pos).ne']
  ring

private theorem half_angleA_mem_Icc (T : Triangle.{u}) :
    (finiteHalf T.angleA).val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) := by
  rw [val_finiteHalf]
  constructor <;> linarith [T.angleA_mem.1, T.angleA_mem.2]

/-- The angle from `AB` to the bisector is exactly the positive half angle. -/
theorem bisector_angle_left (T : Triangle.{u}) :
    interiorAngle (T.B - T.A) (T.bisectorPoint - T.A) T.bisector_cross_left_ne_zero =
      finiteHalf T.angleA := by
  have hi := interiorAngle_mem (T.B - T.A) (T.bisectorPoint - T.A)
    T.bisector_cross_left_ne_zero
  apply finiteCos_strictAntiOn.injOn ⟨hi.1.le, hi.2.le⟩ T.half_angleA_mem_Icc
  rw [finiteCos_interiorAngle, bisector_length, bisectorPoint_sub_A, dot_weighted_right,
    ← modulus_sq (T.B - T.A), modulus_sub_comm T.B T.A, dot_edges, cos_angleA_eq_half]
  change (T.sideB / (T.sideB + T.sideC) * T.sideC ^ 2 +
      T.sideC / (T.sideB + T.sideC) *
        (T.sideB * T.sideC * (2 * finiteCos (finiteHalf T.angleA) ^ 2 - 1))) /
      (T.sideC * (2 * T.sideB * T.sideC / (T.sideB + T.sideC) *
        finiteCos (finiteHalf T.angleA))) = finiteCos (finiteHalf T.angleA)
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne',
    (add_pos T.sideB_pos T.sideC_pos).ne', T.cos_half_angleA_pos.ne']
  ring

/-- The angle from the bisector to `AC` is the same actual positive half angle. -/
theorem bisector_angle_right (T : Triangle.{u}) :
    interiorAngle (T.bisectorPoint - T.A) (T.C - T.A) T.bisector_cross_right_ne_zero =
      finiteHalf T.angleA := by
  have hi := interiorAngle_mem (T.bisectorPoint - T.A) (T.C - T.A)
    T.bisector_cross_right_ne_zero
  apply finiteCos_strictAntiOn.injOn ⟨hi.1.le, hi.2.le⟩ T.half_angleA_mem_Icc
  rw [finiteCos_interiorAngle, bisector_length, bisectorPoint_sub_A, dot_weighted_left,
    ← modulus_sq (T.C - T.A), dot_edges, cos_angleA_eq_half]
  change (T.sideB / (T.sideB + T.sideC) *
        (T.sideB * T.sideC * (2 * finiteCos (finiteHalf T.angleA) ^ 2 - 1)) +
      T.sideC / (T.sideB + T.sideC) * T.sideB ^ 2) /
      ((2 * T.sideB * T.sideC / (T.sideB + T.sideC) *
        finiteCos (finiteHalf T.angleA)) * T.sideB) = finiteCos (finiteHalf T.angleA)
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne',
    (add_pos T.sideB_pos T.sideC_pos).ne', T.cos_half_angleA_pos.ne']
  ring

end Triangle

end
end Surreal.Surcomplex
