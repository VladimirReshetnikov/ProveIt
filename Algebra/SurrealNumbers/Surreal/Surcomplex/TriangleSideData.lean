import Surreal.Algebra.StrictTriangle
import Surreal.Surcomplex.TriangleCircumcircle

/-!
# Triangle inequalities and angle recovery from actual side data

The side lengths of every noncollinear surcomplex triangle satisfy all
three strict triangle inequalities. Its angles are recovered from the
cosine-law quotient by inverse cosine. These are necessary side data and
the angle-recovery clauses of `trigonometry:thm:sss`.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

/-- Every noncollinear actual triangle has the strict inequality for its first side. -/
theorem sideA_lt_add (T : Triangle.{u}) : T.sideA < T.sideB + T.sideC := by
  have he := Complexify.modulus_sub_lt_of_cross_ne_zero (T.B - T.A) (T.C - T.A) T.noncollinear
  change modulus ((T.B - T.A) - (T.C - T.A)) < modulus (T.B - T.A) + modulus (T.C - T.A) at he
  have hd : (T.B - T.A) - (T.C - T.A) = T.B - T.C := by abel
  simpa only [sideA, sideB, sideC, hd, modulus_sub_comm T.B T.A, add_comm] using he

/-- The three strict triangle inequalities hold at arbitrary actual surreal scales. -/
theorem strict_side_inequalities (T : Triangle.{u}) :
    T.sideA < T.sideB + T.sideC ∧ T.sideB < T.sideC + T.sideA ∧
      T.sideC < T.sideA + T.sideB :=
  ⟨T.sideA_lt_add, T.rotate.sideA_lt_add, T.rotate.rotate.sideA_lt_add⟩

/-- The cosine law explicitly recovers the cosine coordinate from the three side lengths. -/
theorem cos_angleA_eq_side_quotient (T : Triangle.{u}) :
    finiteCos T.angleA = (T.sideB ^ 2 + T.sideC ^ 2 - T.sideA ^ 2) /
      (2 * T.sideB * T.sideC) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) T.sideB_pos.ne')
    T.sideC_pos.ne')).mpr
  have he := T.cosine_law
  linear_combination he

/-- A nondegenerate triangle's cosine-law quotient is strictly inside the actual unit interval. -/
theorem cosine_side_quotient_mem_Ioo (T : Triangle.{u}) :
    (T.sideB ^ 2 + T.sideC ^ 2 - T.sideA ^ 2) / (2 * T.sideB * T.sideC) ∈
      Set.Ioo (-1 : SignSequence.{u}) 1 := by
  rw [← cos_angleA_eq_side_quotient]
  have hi := finiteCos_mem_Icc T.angleA
  have hs := T.sin_angleA_pos
  have he := finiteCos_sq_add_finiteSin_sq T.angleA
  constructor <;> nlinarith only [hi.1, hi.2, hs, he, sq_pos_of_pos hs]

/-- Inverse cosine recovers the actual angle, including its infinitesimal part. -/
theorem angleA_eq_arccos_sides (T : Triangle.{u}) :
    T.angleA = arccos ⟨(T.sideB ^ 2 + T.sideC ^ 2 - T.sideA ^ 2) /
      (2 * T.sideB * T.sideC),
      (T.cosine_side_quotient_mem_Ioo).1.le, (T.cosine_side_quotient_mem_Ioo).2.le⟩ := by
  have he := arccos_finiteCos T.angleA ⟨T.angleA_mem.1.le, T.angleA_mem.2.le⟩
  simpa only [T.cos_angleA_eq_side_quotient] using he.symm

/-- Each side is the circumdiameter times the sine of its opposite angle. -/
theorem sideA_eq_circumdiameter_mul_sin (T : Triangle.{u}) :
    T.sideA = 2 * T.circumradius * finiteSin T.angleA :=
  (div_eq_iff T.sin_angleA_pos.ne').mp T.sine_law_circumradius

/-- Equal interior angles force proportional corresponding sides, at all actual scales. -/
theorem exists_positive_side_scale_of_angles_eq (T U : Triangle.{u})
    (hA : T.angleA = U.angleA) (hB : T.angleB = U.angleB) (hC : T.angleC = U.angleC) :
    ∃ k : SignSequence.{u}, 0 < k ∧ T.sideA = k * U.sideA ∧
      T.sideB = k * U.sideB ∧ T.sideC = k * U.sideC := by
  have hside (S V : Triangle.{u}) (hangle : S.angleA = V.angleA) :
      S.sideA = (S.circumradius / V.circumradius) * V.sideA := by
    rw [S.sideA_eq_circumdiameter_mul_sin, V.sideA_eq_circumdiameter_mul_sin, hangle]
    field_simp [V.circumradius_pos.ne']
  refine ⟨T.circumradius / U.circumradius, div_pos T.circumradius_pos U.circumradius_pos,
    hside T U hA, ?_, ?_⟩
  · simpa only [sideA_rotate, circumradius_rotate] using hside T.rotate U.rotate hB
  · simpa only [sideA_rotate, sideB_rotate, circumradius_rotate] using
      hside T.rotate.rotate U.rotate.rotate hC

end Surreal.Surcomplex.Triangle
