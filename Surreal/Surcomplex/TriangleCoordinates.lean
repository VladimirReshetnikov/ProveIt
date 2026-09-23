import Surreal.Surcomplex.RightTriangle
import Surreal.Surcomplex.TriangleHeron

/-!
# Exact geometry of a triangle above a horizontal base

The actual vertices `0`, `L`, and `x + i*y`, with `0 < x < L` and `y > 0`,
give the coordinate formulas used in `trigonometry:thm:flat` and
`trigonometry:eq:flatangles`. The base angles are inverse tangents of their
slopes at every surreal scale. No coordinate or slope is assumed finite.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The actual triangle above a positive horizontal base, with its altitude foot inside the base. -/
def fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x) (hxL : x < L)
    (hy : 0 < y) : Triangle.{u} where
  A := 0
  B := ofReal L
  C := ⟨x, y⟩
  noncollinear := by
    rw [sub_zero, sub_zero, Complexify.cross_def]
    change L * y - 0 * x ≠ 0
    rw [zero_mul, sub_zero]
    exact (mul_pos (hx.trans hxL) hy).ne'

@[simp] theorem A_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) : (fromCoordinates L x y hx hxL hy).A = 0 := rfl

@[simp] theorem B_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).B = ofReal L := rfl

@[simp] theorem C_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).C = ⟨x, y⟩ := rfl

/-- The side opposite the first vertex has the exact coordinate square-root length. -/
@[simp] theorem sideA_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).sideA =
      SignSequence.sqrt ((L - x) ^ 2 + y ^ 2) := by
  apply (SignSequence.sqrt_eq_of_nonneg_sq
    (fromCoordinates L x y hx hxL hy).sideA_pos.le ?_).symm
  change modulus (ofReal L - ⟨x, y⟩) ^ 2 = _
  rw [modulus_sq, normSq_eq]
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    ofReal_re, ofReal_im, zero_sub, neg_sq]

/-- The side opposite the second vertex is the distance from the origin to the upper vertex. -/
@[simp] theorem sideB_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).sideB = SignSequence.sqrt (x ^ 2 + y ^ 2) := by
  apply (SignSequence.sqrt_eq_of_nonneg_sq
    (fromCoordinates L x y hx hxL hy).sideB_pos.le ?_).symm
  change modulus (⟨x, y⟩ - 0) ^ 2 = _
  rw [sub_zero, modulus_sq, normSq_eq]

/-- The horizontal side has the prescribed positive length. -/
@[simp] theorem sideC_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).sideC = L := by
  change modulus (0 - ofReal L) = L
  rw [zero_sub, modulus_neg, modulus_ofReal, abs_of_pos (hx.trans hxL)]

/-- The actual coordinate triangle has area one half of base times height. -/
@[simp] theorem area_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).area = L * y / 2 := by
  change |Complexify.cross (ofReal L - 0) ((⟨x, y⟩ : Surcomplex.{u}) - 0)| / 2 = L * y / 2
  rw [sub_zero, sub_zero, Complexify.cross_def]
  change |L * y - 0 * x| / 2 = L * y / 2
  rw [zero_mul, sub_zero, abs_of_pos (mul_pos (hx.trans hxL) hy)]

/-- The first base-angle cosine is the horizontal displacement divided by its adjacent side. -/
theorem cos_angleA_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    finiteCos (fromCoordinates L x y hx hxL hy).angleA =
      x / SignSequence.sqrt (x ^ 2 + y ^ 2) := by
  have ha : 0 ≤ (L - x) ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb : 0 < x ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg _)
  rw [cos_angleA_eq_side_quotient, sideA_fromCoordinates, sideB_fromCoordinates,
    sideC_fromCoordinates, SignSequence.sqrt_sq ha, SignSequence.sqrt_sq hb.le]
  field_simp [(hx.trans hxL).ne', (SignSequence.sqrt_pos hb).ne']
  ring

/-- The second base-angle cosine uses the positive displacement from the altitude foot to `L`. -/
theorem cos_angleB_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    finiteCos (fromCoordinates L x y hx hxL hy).angleB =
      (L - x) / SignSequence.sqrt ((L - x) ^ 2 + y ^ 2) := by
  have ha : 0 < (L - x) ^ 2 + y ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr hxL)) (sq_nonneg _)
  have hb : 0 ≤ x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [angleB, cos_angleA_eq_side_quotient, sideA_rotate, sideB_rotate, sideC_rotate,
    sideA_fromCoordinates, sideB_fromCoordinates, sideC_fromCoordinates,
    SignSequence.sqrt_sq ha.le, SignSequence.sqrt_sq hb]
  field_simp [(hx.trans hxL).ne', (SignSequence.sqrt_pos ha).ne']
  ring

private theorem angle_eq_arctan_of_cos (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi))
    (p q : SignSequence.{u}) (hp : 0 < p) (hq : 0 < q)
    (hc : finiteCos θ = p / SignSequence.sqrt (p ^ 2 + q ^ 2)) :
    θ = arctan (q / p) := by
  let R := fromPositiveLegs p q hp hq
  have hh : R.sideC = SignSequence.sqrt (p ^ 2 + q ^ 2) :=
    (SignSequence.sqrt_eq_of_nonneg_sq R.sideC_pos.le
      (sideC_sq_fromPositiveLegs p q hp hq)).symm
  have hs : 0 < p ^ 2 + q ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _)
  have hcos : finiteCos R.angleA = p / SignSequence.sqrt (p ^ 2 + q ^ 2) := by
    rw [R.cos_angleA_eq_side_quotient, hh,
      show R.sideA = q from sideA_fromPositiveLegs p q hp hq,
      show R.sideB = p from sideB_fromPositiveLegs p q hp hq]
    rw [SignSequence.sqrt_sq hs.le]
    field_simp [hp.ne', (SignSequence.sqrt_pos hs).ne']
    ring
  have he : θ = R.angleA := finiteCos_strictAntiOn.injOn
    ⟨hθ.1.le, hθ.2.le⟩ ⟨R.angleA_mem.1.le, R.angleA_mem.2.le⟩ (hc.trans hcos.symm)
  exact he.trans (angleA_fromPositiveLegs p q hp hq)

/-- The first base angle is inverse tangent of its slope, even for infinite slopes. -/
theorem angleA_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).angleA = arctan (y / x) :=
  angle_eq_arctan_of_cos _ (fromCoordinates L x y hx hxL hy).angleA_mem x y hx hy
    (cos_angleA_fromCoordinates L x y hx hxL hy)

/-- The second base angle is inverse tangent of the slope from the other endpoint. -/
theorem angleB_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).angleB = arctan (y / (L - x)) :=
  angle_eq_arctan_of_cos _ (fromCoordinates L x y hx hxL hy).rotate.angleA_mem
    (L - x) y (sub_pos.mpr hxL) hy (cos_angleB_fromCoordinates L x y hx hxL hy)

/-- The upper angle is exactly pi minus the two inverse-tangent base angles. -/
theorem angleC_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).angleC = SignSequence.finiteOfReal Real.pi -
      arctan (y / x) - arctan (y / (L - x)) := by
  rw [← angleA_fromCoordinates L x y hx hxL hy,
    ← angleB_fromCoordinates L x y hx hxL hy]
  apply ArchimedeanClass.FiniteElement.ext
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val)
    (fromCoordinates L x y hx hxL hy).angle_sum
  change _ + _ + _ = SignSequence.ofReal Real.pi at he
  change _ = SignSequence.ofReal Real.pi - _ - _
  linarith only [he]

/-- The circumradius is the product of the nonhorizontal sides divided by twice the height. -/
theorem circumradius_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).circumradius =
      (fromCoordinates L x y hx hxL hy).sideA *
        (fromCoordinates L x y hx hxL hy).sideB / (2 * y) := by
  rw [circumradius_eq_side_product, sideC_fromCoordinates, area_fromCoordinates]
  field_simp [(hx.trans hxL).ne', hy.ne']
  ring

/-- The inradius is base times height divided by the actual perimeter. -/
theorem inradius_fromCoordinates (L x y : SignSequence.{u}) (hx : 0 < x)
    (hxL : x < L) (hy : 0 < y) :
    (fromCoordinates L x y hx hxL hy).inradius = L * y /
      ((fromCoordinates L x y hx hxL hy).sideA +
        (fromCoordinates L x y hx hxL hy).sideB + L) := by
  rw [inradius, semiperimeter, sideC_fromCoordinates, area_fromCoordinates]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : SignSequence.{u}) ≠ 0) _ _

end
end Surreal.Surcomplex.Triangle
