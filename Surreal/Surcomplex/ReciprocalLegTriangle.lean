import Surreal.Surcomplex.RightTriangle
import Surreal.Surcomplex.TriangleHeron

/-!
# Exact geometry of reciprocal-leg triangles

The prescribed vertices `0`, `L`, and `L + i/L` in
`trigonometry:ex:infinite` form an actual triangle for every positive
surreal `L`. Its area is exactly one half. The companion triangle has
vertices `0`, `L`, and `i/L`, as in the source's ordinal-omega example;
its vertex labels and angle permutation are recorded explicitly.
-/

universe u

namespace Surreal.Surcomplex.ReciprocalLegTriangle

open Foundations

noncomputable section

variable (L : SignSequence.{u}) (hL : 0 < L)

/-- The right triangle with exactly the three vertices prescribed in the source. -/
def triangle : Triangle.{u} where
  A := 0
  B := ofReal L
  C := ⟨L, L⁻¹⟩
  noncollinear := by
    rw [sub_zero, sub_zero, Complexify.cross_def]
    change L * L⁻¹ - 0 * L ≠ 0
    rw [zero_mul, sub_zero, mul_inv_cancel₀ hL.ne']
    exact one_ne_zero

@[simp] theorem vertexA : (triangle L hL).A = 0 := rfl

@[simp] theorem vertexB : (triangle L hL).B = ofReal L := rfl

@[simp] theorem vertexC : (triangle L hL).C = ⟨L, L⁻¹⟩ := rfl

@[simp] theorem sideA : (triangle L hL).sideA = L⁻¹ := by
  change modulus (ofReal L - (⟨L, L⁻¹⟩ : Surcomplex.{u})) = L⁻¹
  apply modulus_eq_of_nonneg_sq (inv_pos.mpr hL).le
  rw [normSq_eq]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    ofReal_re, ofReal_im, sub_self, zero_sub, neg_sq]
  ring

@[simp] theorem sideB : (triangle L hL).sideB =
    SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2) := by
  apply (SignSequence.sqrt_eq_of_nonneg_sq (triangle L hL).sideB_pos.le ?_).symm
  change modulus ((⟨L, L⁻¹⟩ : Surcomplex.{u}) - 0) ^ 2 = _
  rw [sub_zero, modulus_sq, normSq_eq]

@[simp] theorem sideC : (triangle L hL).sideC = L := by
  change modulus (0 - ofReal L) = L
  rw [zero_sub, modulus_neg, modulus_ofReal, abs_of_pos hL]

/-- Reciprocal positive legs give the ordinary area one half at every scale. -/
@[simp] theorem area : (triangle L hL).area = 1 / 2 := by
  change |Complexify.cross (ofReal L - 0)
    ((⟨L, L⁻¹⟩ : Surcomplex.{u}) - 0)| / 2 = 1 / 2
  rw [sub_zero, sub_zero, Complexify.cross_def]
  change |L * L⁻¹ - 0 * L| / 2 = 1 / 2
  rw [zero_mul, sub_zero, mul_inv_cancel₀ hL.ne', abs_one]

/-- The angle at the translated right vertex is exactly pi divided by two. -/
@[simp] theorem angleB : (triangle L hL).angleB =
    SignSequence.finiteOfReal (Real.pi / 2) := by
  have he : (triangle L hL).rotate.rotate.angleC =
      SignSequence.finiteOfReal (Real.pi / 2) := by
    apply (Triangle.right_angleC_iff_pythagoras _).mpr
    simp only [Triangle.sideA_rotate, Triangle.sideB_rotate, Triangle.sideC_rotate,
      sideA, sideB, sideC]
    exact SignSequence.sqrt_sq (add_nonneg (sq_nonneg _) (sq_nonneg _))
  simpa only [Triangle.angleC_rotate, Triangle.angleA_rotate] using he

/-- The angle opposite the reciprocal leg is the inverse tangent of the inverse square. -/
@[simp] theorem angleA : (triangle L hL).angleA = arctan ((L⁻¹) ^ 2) := by
  have hr : (triangle L hL).rotate.rotate.angleC =
      SignSequence.finiteOfReal (Real.pi / 2) := by
    simpa only [Triangle.angleC_rotate, Triangle.angleA_rotate] using angleB L hL
  have he := (triangle L hL).rotate.rotate.angleB_eq_arctan_of_right hr
  simpa only [Triangle.angleB_rotate, Triangle.angleC_rotate,
    Triangle.sideA_rotate, Triangle.sideB_rotate, Triangle.sideC_rotate,
    sideA, sideC, div_eq_mul_inv, pow_two] using he

/-- The remaining acute angle is the exact complement of the small angle. -/
@[simp] theorem angleC : (triangle L hL).angleC =
    SignSequence.finiteOfReal (Real.pi / 2) - arctan ((L⁻¹) ^ 2) := by
  apply ArchimedeanClass.FiniteElement.ext
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val)
    (triangle L hL).angle_sum
  rw [angleA, angleB] at he
  change _ + SignSequence.ofReal (Real.pi / 2) + _ = SignSequence.ofReal Real.pi at he
  change _ = SignSequence.ofReal (Real.pi / 2) - _
  rw [map_div₀, map_ofNat] at he ⊢
  linarith only [he]

/-- The hypotenuse can be normalized by the positive long leg without a finiteness assumption. -/
theorem hypotenuse_factor (hL : 0 < L) : SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2) =
    L * SignSequence.sqrt (1 + (L⁻¹) ^ 4) := by
  apply SignSequence.sqrt_eq_of_nonneg_sq
    (mul_nonneg hL.le (SignSequence.sqrt_nonneg _))
  rw [mul_pow, SignSequence.sqrt_sq (by positivity)]
  field_simp [hL.ne']

/-- The circumradius is exactly half the hypotenuse. -/
theorem circumradius : (triangle L hL).circumradius =
    SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2) / 2 := by
  rw [Triangle.circumradius_eq_side_product, sideA, sideB, sideC, area]
  field_simp [hL.ne']
  ring

/-- The inradius is half the sum of the legs minus half the hypotenuse. -/
theorem inradius : (triangle L hL).inradius =
    (L + L⁻¹ - SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2)) / 2 := by
  have hs := SignSequence.sqrt_sq (add_nonneg (sq_nonneg L) (sq_nonneg (L⁻¹)))
  have hd : L⁻¹ + SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2) + L ≠ 0 :=
    (add_pos (add_pos_of_pos_of_nonneg (inv_pos.mpr hL)
      (SignSequence.sqrt_nonneg _)) hL).ne'
  rw [Triangle.inradius, Triangle.semiperimeter, area, sideA, sideB, sideC]
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : SignSequence.{u}) ≠ 0)]
  apply (div_eq_div_iff hd (by norm_num)).mpr
  nlinarith only [hs, mul_inv_cancel₀ hL.ne']

/-- The source's companion placement puts the right angle at zero. -/
def companion : Triangle.{u} :=
  (Triangle.fromPositiveLegs L L⁻¹ hL (inv_pos.mpr hL)).rotate.rotate

@[simp] theorem companion_vertexA : (companion L hL).A = 0 := rfl

@[simp] theorem companion_vertexB : (companion L hL).B = ofReal L := rfl

@[simp] theorem companion_vertexC : (companion L hL).C = ofReal L⁻¹ * I := rfl

@[simp] theorem companion_sideA : (companion L hL).sideA =
    SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2) := by
  apply (SignSequence.sqrt_eq_of_nonneg_sq (companion L hL).sideA_pos.le ?_).symm
  exact Triangle.sideC_sq_fromPositiveLegs L L⁻¹ hL (inv_pos.mpr hL)

@[simp] theorem companion_sideB : (companion L hL).sideB = L⁻¹ :=
  Triangle.sideA_fromPositiveLegs L L⁻¹ hL (inv_pos.mpr hL)

@[simp] theorem companion_sideC : (companion L hL).sideC = L :=
  Triangle.sideB_fromPositiveLegs L L⁻¹ hL (inv_pos.mpr hL)

@[simp] theorem companion_area : (companion L hL).area = 1 / 2 := by
  change |Complexify.cross (ofReal L - 0) (ofReal L⁻¹ * I - 0)| / 2 = 1 / 2
  rw [sub_zero, sub_zero, Complexify.cross_def]
  simp only [ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, add_zero, mul_inv_cancel₀ hL.ne', abs_one]

@[simp] theorem companion_angleA : (companion L hL).angleA =
    SignSequence.finiteOfReal (Real.pi / 2) :=
  Triangle.right_fromPositiveLegs L L⁻¹ hL (inv_pos.mpr hL)

@[simp] theorem companion_angleB : (companion L hL).angleB = arctan ((L⁻¹) ^ 2) := by
  have he := Triangle.angleA_fromPositiveLegs L L⁻¹ hL (inv_pos.mpr hL)
  simpa only [companion, Triangle.angleB_rotate, Triangle.angleC_rotate,
    div_eq_mul_inv, pow_two] using he

@[simp] theorem companion_angleC : (companion L hL).angleC =
    SignSequence.finiteOfReal (Real.pi / 2) - arctan ((L⁻¹) ^ 2) := by
  apply ArchimedeanClass.FiniteElement.ext
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val)
    (companion L hL).angle_sum
  rw [companion_angleA, companion_angleB] at he
  change SignSequence.ofReal (Real.pi / 2) + _ + _ = SignSequence.ofReal Real.pi at he
  change _ = SignSequence.ofReal (Real.pi / 2) - _
  rw [map_div₀, map_ofNat] at he ⊢
  linarith only [he]

theorem companion_circumradius : (companion L hL).circumradius =
    SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2) / 2 := by
  rw [Triangle.circumradius_eq_side_product,
    companion_sideA, companion_sideB, companion_sideC, companion_area]
  field_simp [hL.ne']
  ring

theorem companion_inradius : (companion L hL).inradius =
    (L + L⁻¹ - SignSequence.sqrt (L ^ 2 + (L⁻¹) ^ 2)) / 2 := by
  rw [← inradius L hL, Triangle.inradius, Triangle.inradius,
    Triangle.semiperimeter, Triangle.semiperimeter,
    companion_area, area, companion_sideA, companion_sideB, companion_sideC,
    sideA, sideB, sideC]
  congr 2
  ring

end
end Surreal.Surcomplex.ReciprocalLegTriangle
