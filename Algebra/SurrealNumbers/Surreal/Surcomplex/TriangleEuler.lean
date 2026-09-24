import Surreal.Algebra.WeightedVariance
import Surreal.Surcomplex.TriangleIncenter
import Surreal.Surcomplex.TriangleRadiusInequality

/-!
# Euler's identity for the actual triangle centers

The weighted variance identity, applied after translating the circumcenter
to zero, gives the exact distance between the actual incenter and
circumcenter. Together with the positive side-defect identity this proves
`trigonometry:thm:euler` and `trigonometry:eq:euler`, including the
equilateral equality case, without a restriction on surreal scales.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- Translating a side-weighted sum translates its barycenter by the same amount. -/
theorem weighted_vertex_displacement (T : Triangle.{u}) (P : Surcomplex.{u}) :
    T.sideA • (P - T.A) + T.sideB • (P - T.B) + T.sideC • (P - T.C) =
      (2 * T.semiperimeter) • (P - T.incenter) := by
  apply QuadraticAlgebra.ext <;>
    simp only [incenter, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
      QuadraticAlgebra.im_smul, smul_eq_mul] <;>
    field_simp [T.semiperimeter_pos.ne'] <;> dsimp [semiperimeter] <;> ring

/-- The variance identity gives the squared center distance before substituting both radii. -/
theorem center_distance_sq_eq_side_product (T : Triangle.{u}) :
    modulus (T.circumcenter - T.incenter) ^ 2 = T.circumradius ^ 2 -
      T.sideA * T.sideB * T.sideC / (2 * T.semiperimeter) := by
  have hv := Complexify.normSq_weighted_variance_three T.sideA T.sideB T.sideC
    (T.circumcenter - T.A) (T.circumcenter - T.B) (T.circumcenter - T.C)
  change (T.sideA + T.sideB + T.sideC) *
      (T.sideA * normSq (T.circumcenter - T.A) +
        T.sideB * normSq (T.circumcenter - T.B) +
        T.sideC * normSq (T.circumcenter - T.C)) =
    normSq (T.sideA • (T.circumcenter - T.A) +
      T.sideB • (T.circumcenter - T.B) + T.sideC • (T.circumcenter - T.C)) +
    T.sideA * T.sideB * normSq ((T.circumcenter - T.A) - (T.circumcenter - T.B)) +
    T.sideA * T.sideC * normSq ((T.circumcenter - T.A) - (T.circumcenter - T.C)) +
    T.sideB * T.sideC * normSq ((T.circumcenter - T.B) - (T.circumcenter - T.C)) at hv
  have hAB : normSq ((T.circumcenter - T.A) - (T.circumcenter - T.B)) =
      T.sideC ^ 2 := by
    have he : (T.circumcenter - T.A) - (T.circumcenter - T.B) = T.B - T.A := by abel
    rw [he, ← modulus_sq, modulus_sub_comm T.B T.A]
    rfl
  have hAC : normSq ((T.circumcenter - T.A) - (T.circumcenter - T.C)) =
      T.sideB ^ 2 := by
    have he : (T.circumcenter - T.A) - (T.circumcenter - T.C) = T.C - T.A := by abel
    rw [he, ← modulus_sq]
    rfl
  have hBC : normSq ((T.circumcenter - T.B) - (T.circumcenter - T.C)) =
      T.sideA ^ 2 := by
    have he : (T.circumcenter - T.B) - (T.circumcenter - T.C) = T.C - T.B := by abel
    rw [he, ← modulus_sq, modulus_sub_comm T.C T.B]
    rfl
  have hs : normSq ((2 * T.semiperimeter) • (T.circumcenter - T.incenter)) =
      (2 * T.semiperimeter) ^ 2 * normSq (T.circumcenter - T.incenter) :=
    Complexify.normSq_smul _ _
  rw [hAB, hAC, hBC, T.weighted_vertex_displacement, hs,
    ← modulus_sq, ← modulus_sq, ← modulus_sq, ← modulus_sq,
    T.circumcenter_equidistant.1, T.circumcenter_equidistant.2.1,
    T.circumcenter_equidistant.2.2] at hv
  have he : (2 * T.semiperimeter) ^ 2 * modulus (T.circumcenter - T.incenter) ^ 2 =
      (2 * T.semiperimeter) ^ 2 * T.circumradius ^ 2 -
        (2 * T.semiperimeter) * (T.sideA * T.sideB * T.sideC) := by
    dsimp [semiperimeter] at hv ⊢
    linear_combination -hv
  have hden : (2 * T.semiperimeter) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (by norm_num) T.semiperimeter_pos.ne')
  apply mul_left_cancel₀ hden
  rw [he]
  field_simp [T.semiperimeter_pos.ne']

/-- Euler's actual center-distance identity, at arbitrary infinite or infinitesimal scale. -/
theorem euler (T : Triangle.{u}) :
    modulus (T.circumcenter - T.incenter) ^ 2 =
      T.circumradius * (T.circumradius - 2 * T.inradius) := by
  have hr : T.sideA * T.sideB * T.sideC / (2 * T.semiperimeter) =
      2 * T.circumradius * T.inradius := by
    rw [T.circumradius_eq_side_product, inradius]
    field_simp [T.area_pos.ne', T.semiperimeter_pos.ne']
    ring
  rw [T.center_distance_sq_eq_side_product, hr]
  ring

/-- The incenter and circumcenter coincide exactly for equilateral triangles. -/
theorem circumcenter_eq_incenter_iff (T : Triangle.{u}) :
    T.circumcenter = T.incenter ↔ T.sideA = T.sideB ∧ T.sideB = T.sideC := by
  constructor
  · intro hc
    have he := T.euler
    rw [hc, sub_self, modulus_zero, zero_pow (by norm_num : 2 ≠ 0)] at he
    have hr := (mul_eq_zero.mp he.symm).resolve_left T.circumradius_pos.ne'
    exact T.circumradius_eq_twice_inradius_iff.mp (sub_eq_zero.mp hr)
  · intro hs
    have hr := T.circumradius_eq_twice_inradius_iff.mpr hs
    apply sub_eq_zero.mp
    apply (modulus_eq_zero_iff _).mp
    apply sq_eq_zero_iff.mp
    rw [T.euler, hr, sub_self, mul_zero]

end
end Surreal.Surcomplex.Triangle
