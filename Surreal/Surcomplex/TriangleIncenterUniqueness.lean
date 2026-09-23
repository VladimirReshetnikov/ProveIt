import Surreal.Surcomplex.TriangleIncenter

/-!
# Uniqueness of the actual interior incircle center

An interior point here means a point with strictly positive barycentric
coordinates. Its three side distances determine those coordinates, so
an interior point equidistant from the side lines is the actual incenter.
This supplies the uniqueness implicit in `trigonometry:thm:heron` and
`trigonometry:eq:incenter`, without a topology or a finite-scale assumption.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The determinant against a side extracts the opposite barycentric weight. -/
theorem cross_barycentric_sideC (T : Triangle.{u}) (a b c : SignSequence.{u})
    (hs : a + b + c = 1) :
    Complexify.cross (T.B - T.A) (a • T.A + b • T.B + c • T.C - T.A) =
      c * Complexify.cross (T.B - T.A) (T.C - T.A) := by
  have ha : a = 1 - b - c := by linarith only [hs]
  rw [ha]
  simp only [Complexify.cross_def, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, smul_eq_mul]
  ring

/-- For nonnegative opposite weight, the side distance is the weight times its altitude. -/
theorem lineDistance_barycentric_sideC (T : Triangle.{u}) (a b c : SignSequence.{u})
    (hc : 0 ≤ c) (hs : a + b + c = 1) :
    Complexify.lineDistance T.A (T.B - T.A) (a • T.A + b • T.B + c • T.C) =
      c * (2 * T.area) / T.sideC := by
  rw [Complexify.lineDistance_eq_cross_div _ _ _
    (left_ne_zero_of_cross_ne_zero T.noncollinear), T.cross_barycentric_sideC a b c hs,
    abs_mul, abs_of_nonneg hc]
  change c * |Complexify.cross (T.B - T.A) (T.C - T.A)| / modulus (T.B - T.A) =
    c * (2 * (|Complexify.cross (T.B - T.A) (T.C - T.A)| / 2)) / modulus (T.A - T.B)
  rw [modulus_sub_comm T.B T.A]
  ring

/-- An interior point with equal perpendicular distances to the three sides is the incenter. -/
theorem eq_incenter_of_isInteriorPoint_of_equidistant (T : Triangle.{u})
    (P : Surcomplex.{u}) (hP : T.IsInteriorPoint P)
    (hAB : Complexify.lineDistance T.A (T.B - T.A) P =
      Complexify.lineDistance T.B (T.C - T.B) P)
    (hBC : Complexify.lineDistance T.B (T.C - T.B) P =
      Complexify.lineDistance T.C (T.A - T.C) P) : P = T.incenter := by
  obtain ⟨a, b, c, ha, hb, hc, hs, hp⟩ := hP
  have hdC : Complexify.lineDistance T.A (T.B - T.A) P =
      c * (2 * T.area) / T.sideC := by
    rw [hp]
    exact T.lineDistance_barycentric_sideC a b c hc.le hs
  have hdA : Complexify.lineDistance T.B (T.C - T.B) P =
      a * (2 * T.area) / T.sideA := by
    have he : P = b • T.B + c • T.C + a • T.A := by rw [hp]; abel
    rw [he]
    have hsum : b + c + a = 1 := by linarith only [hs]
    have hd := T.rotate.lineDistance_barycentric_sideC b c a ha.le hsum
    rw [area_rotate, sideC_rotate] at hd
    exact hd
  have hdB : Complexify.lineDistance T.C (T.A - T.C) P =
      b * (2 * T.area) / T.sideB := by
    have he : P = c • T.C + a • T.A + b • T.B := by rw [hp]; abel
    rw [he]
    have hsum : c + a + b = 1 := by linarith only [hs]
    have hd := T.rotate.rotate.lineDistance_barycentric_sideC c a b hb.le hsum
    rw [area_rotate, area_rotate, sideC_rotate, sideA_rotate] at hd
    exact hd
  let r := Complexify.lineDistance T.A (T.B - T.A) P
  have haD : a * (2 * T.area) = r * T.sideA :=
    ((eq_div_iff T.sideA_pos.ne').mp (hAB.trans hdA)).symm
  have hbD : b * (2 * T.area) = r * T.sideB :=
    ((eq_div_iff T.sideB_pos.ne').mp ((hAB.trans hBC).trans hdB)).symm
  have hcD : c * (2 * T.area) = r * T.sideC :=
    ((eq_div_iff T.sideC_pos.ne').mp hdC).symm
  have hr : r * (2 * T.semiperimeter) = 2 * T.area := by
    dsimp only [semiperimeter]
    linear_combination (2 * T.area) * hs - haD - hbD - hcD
  have hden : 2 * T.semiperimeter ≠ 0 :=
    (mul_pos (by norm_num) T.semiperimeter_pos).ne'
  have harea : 2 * T.area ≠ 0 := (mul_pos (by norm_num) T.area_pos).ne'
  have weight (x side : SignSequence.{u}) (hx : x * (2 * T.area) = r * side) :
      x = side / (2 * T.semiperimeter) := by
    apply (eq_div_iff hden).mpr
    apply mul_right_cancel₀ harea
    linear_combination (2 * T.semiperimeter) * hx + side * hr
  rw [hp, weight a T.sideA haD, weight b T.sideB hbD, weight c T.sideC hcD]
  simp only [incenter, smul_add, smul_smul, div_eq_mul_inv, mul_comm]

/-- Exactly one positive-barycentric point is equidistant from the three side lines. -/
theorem existsUnique_incenter (T : Triangle.{u}) :
    ∃! P : Surcomplex.{u}, T.IsInteriorPoint P ∧
      Complexify.lineDistance T.A (T.B - T.A) P =
        Complexify.lineDistance T.B (T.C - T.B) P ∧
      Complexify.lineDistance T.B (T.C - T.B) P =
        Complexify.lineDistance T.C (T.A - T.C) P := by
  obtain ⟨hA, hB, hC⟩ := T.lineDistance_incenter_cyclic
  refine ⟨T.incenter, ⟨T.incenter_isInteriorPoint, hA.trans hB.symm, hB.trans hC.symm⟩, ?_⟩
  rintro P ⟨hP, hAB, hBC⟩
  exact T.eq_incenter_of_isInteriorPoint_of_equidistant P hP hAB hBC

/-- The interior incircle has a unique actual center and positive surreal radius. -/
theorem existsUnique_incircle (T : Triangle.{u}) :
    ∃! circle : Surcomplex.{u} × SignSequence.{u},
      T.IsInteriorPoint circle.1 ∧ 0 < circle.2 ∧
        Complexify.lineDistance T.A (T.B - T.A) circle.1 = circle.2 ∧
        Complexify.lineDistance T.B (T.C - T.B) circle.1 = circle.2 ∧
        Complexify.lineDistance T.C (T.A - T.C) circle.1 = circle.2 := by
  refine ⟨(T.incenter, T.inradius),
    ⟨T.incenter_isInteriorPoint, T.inradius_pos, T.lineDistance_incenter_cyclic⟩, ?_⟩
  rintro ⟨P, r⟩ ⟨hP, _, hAB, hBC, hCA⟩
  have hp : P = T.incenter := T.eq_incenter_of_isInteriorPoint_of_equidistant P hP
    (hAB.trans hBC.symm) (hBC.trans hCA.symm)
  apply Prod.ext hp
  rw [hp, T.lineDistance_incenter] at hAB
  exact hAB.symm

end
end Surreal.Surcomplex.Triangle
