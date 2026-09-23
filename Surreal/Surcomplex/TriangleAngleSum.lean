import Surreal.Surcomplex.InteriorAngle
import Surreal.Surcomplex.DirectionNormalization
import Surreal.Surcomplex.AngleSumKernel

/-!
# Exact angle sums for noncollinear surcomplex triangles

The cyclic determinants of a triangle have the same sign. Its three
interior phases are the corresponding relative unit directions, or all
their conjugates, and their product is minus one. The phase kernel then
proves `trigonometry:thm:anglesum` as an equality of actual finite surreal
angles, at arbitrary side and area scales.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Relative unit directions have the normalized dot and oriented determinant coordinates. -/
theorem unitDirection_div_eq (z w : Surcomplex.{u}ˣ) :
    (unitDirection (w / z)).val =
      conj (z : Surcomplex.{u}) * (w : Surcomplex.{u}) / ofReal (modulus z * modulus w) := by
  have he : unitDirection (w / z) = (unitDirection z)⁻¹ * unitDirection w := by
    rw [map_div, div_eq_mul_inv, mul_comm]
  rw [he, coe_unitCircle_relative, coe_unitDirection, coe_unitDirection,
    map_div₀, conj_ofReal, div_mul_div_comm, ← map_mul]

/-- Positive orientation identifies the interior phase with the relative unit direction. -/
theorem interiorDirection_eq_unitDirection (z w : Surcomplex.{u}ˣ)
    (h : 0 < Complexify.cross (z : Surcomplex.{u}) (w : Surcomplex.{u})) :
    interiorDirection z w = (unitDirection (w / z)).val := by
  rw [unitDirection_div_eq]
  have hi : (ofReal (modulus z * modulus w))⁻¹ =
      ofReal ((modulus z * modulus w)⁻¹) := (map_inv₀ ofReal _).symm
  apply QuadraticAlgebra.ext
  · simp only [interiorDirection, div_eq_mul_inv, hi, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, conj_re, conj_im, Complexify.dot_def]
    ring
  · simp only [interiorDirection]
    rw [abs_of_pos h]
    simp only [div_eq_mul_inv, hi, mul_im, ofReal_re,
      ofReal_im, mul_zero, zero_add, conj_re, conj_im, Complexify.cross_def]
    ring

/-- Negative orientation identifies the interior phase with the conjugate relative direction. -/
theorem interiorDirection_eq_conj_unitDirection (z w : Surcomplex.{u}ˣ)
    (h : Complexify.cross (z : Surcomplex.{u}) (w : Surcomplex.{u}) < 0) :
    interiorDirection z w = conj (unitDirection (w / z)).val := by
  rw [unitDirection_div_eq]
  have hi : (ofReal (modulus z * modulus w))⁻¹ =
      ofReal ((modulus z * modulus w)⁻¹) := (map_inv₀ ofReal _).symm
  apply QuadraticAlgebra.ext
  · simp only [interiorDirection, conj_re, div_eq_mul_inv, hi, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, conj_im, Complexify.dot_def]
    ring
  · simp only [interiorDirection]
    rw [abs_of_neg h]
    simp only [conj_im, div_eq_mul_inv, hi, mul_im,
      ofReal_re, ofReal_im, mul_zero, zero_add, conj_re, Complexify.cross_def]
    ring

/-- The oriented double area is invariant under cyclic permutation of triangle vertices. -/
theorem cross_triangle_cyclic (A B C : Surcomplex.{u}) :
    Complexify.cross (C - B) (A - B) = Complexify.cross (B - A) (C - A) := by
  simp only [Complexify.cross_def, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub]
  ring

/-- The next cyclic vertex of a noncollinear triangle remains noncollinear. -/
theorem cross_triangle_cyclic_ne_zero (A B C : Surcomplex.{u})
    (h : Complexify.cross (B - A) (C - A) ≠ 0) :
    Complexify.cross (C - B) (A - B) ≠ 0 := by
  rwa [cross_triangle_cyclic]

/-- The product of the three positive interior phases is a half turn, for either orientation. -/
theorem interiorDirection_triangle_product (A B C : Surcomplex.{u})
    (h : Complexify.cross (B - A) (C - A) ≠ 0) :
    interiorDirection (B - A) (C - A) * interiorDirection (C - B) (A - B) *
      interiorDirection (A - C) (B - C) = -1 := by
  have hB := cross_triangle_cyclic_ne_zero A B C h
  let u : Surcomplex.{u}ˣ := Units.mk0 (B - A) (left_ne_zero_of_cross_ne_zero h)
  let w : Surcomplex.{u}ˣ := Units.mk0 (C - A) (right_ne_zero_of_cross_ne_zero h)
  let v : Surcomplex.{u}ˣ := Units.mk0 (C - B) (left_ne_zero_of_cross_ne_zero hB)
  have hu : (u : Surcomplex.{u}) = B - A := rfl
  have hw : (w : Surcomplex.{u}) = C - A := rfl
  have hv : (v : Surcomplex.{u}) = C - B := rfl
  have hnu : ((-u : Surcomplex.{u}ˣ) : Surcomplex.{u}) = A - B := by simp [hu]
  have hnw : ((-w : Surcomplex.{u}ˣ) : Surcomplex.{u}) = A - C := by simp [hw]
  have hnv : ((-v : Surcomplex.{u}ˣ) : Surcomplex.{u}) = B - C := by simp [hv]
  have hp : (w / u) * ((-u) / v) * ((-v) / (-w)) = (-1 : Surcomplex.{u}ˣ) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_neg, Units.val_one]
    field_simp
  have hd : (unitDirection (w / u)).val * (unitDirection ((-u) / v)).val *
      (unitDirection ((-v) / (-w))).val = (-1 : Surcomplex.{u}) := by
    have he := congrArg (fun t : Surcomplex.{u}ˣ => (unitDirection t).val) hp
    simpa only [map_mul, Submonoid.coe_mul, coe_unitDirection, Units.val_neg,
      Units.val_one, modulus_neg, modulus_one, map_one, div_one] using he
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have hnB : Complexify.cross (C - B) (A - B) < 0 := by
      rwa [cross_triangle_cyclic]
    have hnC : Complexify.cross (A - C) (B - C) < 0 := by
      rwa [cross_triangle_cyclic]
    rw [← hu, ← hw, ← hv, ← hnu, ← hnw, ← hnv]
    rw [interiorDirection_eq_conj_unitDirection u w hneg,
      interiorDirection_eq_conj_unitDirection v (-u) (by simpa only [hv, hnu] using hnB),
      interiorDirection_eq_conj_unitDirection (-w) (-v) (by simpa only [hnw, hnv] using hnC),
      ← map_mul, ← map_mul, hd, map_neg, map_one]
  · have hpB : 0 < Complexify.cross (C - B) (A - B) := by
      rwa [cross_triangle_cyclic]
    have hpC : 0 < Complexify.cross (A - C) (B - C) := by
      rwa [cross_triangle_cyclic]
    rw [← hu, ← hw, ← hv, ← hnu, ← hnw, ← hnv]
    rw [interiorDirection_eq_unitDirection u w hpos,
      interiorDirection_eq_unitDirection v (-u) (by simpa only [hv, hnu] using hpB),
      interiorDirection_eq_unitDirection (-w) (-v) (by simpa only [hnw, hnv] using hpC)]
    exact hd

/-- Every noncollinear actual surcomplex triangle has angle sum exactly `pi`. -/
theorem interiorAngle_triangle_sum (A B C : Surcomplex.{u})
    (h : Complexify.cross (B - A) (C - A) ≠ 0) :
    interiorAngle (B - A) (C - A) h +
      interiorAngle (C - B) (A - B) (cross_triangle_cyclic_ne_zero A B C h) +
      interiorAngle (A - C) (B - C)
        (cross_triangle_cyclic_ne_zero B C A (cross_triangle_cyclic_ne_zero A B C h)) =
      SignSequence.finiteOfReal Real.pi := by
  have hB := cross_triangle_cyclic_ne_zero A B C h
  have hC := cross_triangle_cyclic_ne_zero B C A hB
  have hα := interiorAngle_mem (B - A) (C - A) h
  have hβ := interiorAngle_mem (C - B) (A - B) hB
  have hγ := interiorAngle_mem (A - C) (B - C) hC
  apply finiteAngle_eq_pi_of_phase_eq_neg_one
  · change 0 < (interiorAngle (B - A) (C - A) h).val +
      (interiorAngle (C - B) (A - B) hB).val + (interiorAngle (A - C) (B - C) hC).val
    linarith only [hα.1, hβ.1, hγ.1]
  · change (interiorAngle (B - A) (C - A) h).val +
      (interiorAngle (C - B) (A - B) hB).val + (interiorAngle (A - C) (B - C) hC).val < _
    linarith only [hα.2, hβ.2, hγ.2]
  · rw [finitePhase_add, finitePhase_add, finitePhase_interiorAngle,
      finitePhase_interiorAngle, finitePhase_interiorAngle]
    exact interiorDirection_triangle_product A B C h

end
end Surreal.Surcomplex
