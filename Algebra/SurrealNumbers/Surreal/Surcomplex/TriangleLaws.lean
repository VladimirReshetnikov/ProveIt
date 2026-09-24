import Surreal.Surcomplex.TriangleAngleSum

/-!
# Cosine, sine and tangent laws for actual surcomplex triangles

Package a noncollinear triangle and its actual side lengths, area and
interior angles. Cyclic permutation gives all three cosine and area laws,
and the common sine-law value. Positive half-angle bounds justify every
division in the tangent law of `trigonometry:thm:trianglelaws` and
`trigonometry:eq:trianglelaws`. Circumcircles are constructed separately.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Reversing a displacement does not change its actual surreal length. -/
theorem modulus_sub_comm (z w : Surcomplex.{u}) : modulus (z - w) = modulus (w - z) := by
  rw [← neg_sub w z, modulus_neg]

/-- A triangle of actual surcomplex points with nonzero oriented area. -/
structure Triangle where
  A : Surcomplex.{u}
  B : Surcomplex.{u}
  C : Surcomplex.{u}
  noncollinear : Complexify.cross (B - A) (C - A) ≠ 0

namespace Triangle

/-- Cyclic permutation preserves noncollinearity. -/
def rotate (T : Triangle.{u}) : Triangle.{u} :=
  ⟨T.B, T.C, T.A, cross_triangle_cyclic_ne_zero T.A T.B T.C T.noncollinear⟩

@[simp] theorem rotate_rotate_rotate (T : Triangle.{u}) : T.rotate.rotate.rotate = T := by
  cases T
  rfl

def sideA (T : Triangle.{u}) : SignSequence.{u} := modulus (T.B - T.C)
def sideB (T : Triangle.{u}) : SignSequence.{u} := modulus (T.C - T.A)
def sideC (T : Triangle.{u}) : SignSequence.{u} := modulus (T.A - T.B)
def area (T : Triangle.{u}) : SignSequence.{u} := triangleArea (T.B - T.A) (T.C - T.A)
def angleA (T : Triangle.{u}) : SignSequence.FiniteElement.{u} :=
  interiorAngle (T.B - T.A) (T.C - T.A) T.noncollinear
def angleB (T : Triangle.{u}) : SignSequence.FiniteElement.{u} := T.rotate.angleA
def angleC (T : Triangle.{u}) : SignSequence.FiniteElement.{u} := T.rotate.rotate.angleA

@[simp] theorem sideA_rotate (T : Triangle.{u}) : T.rotate.sideA = T.sideB := rfl
@[simp] theorem sideB_rotate (T : Triangle.{u}) : T.rotate.sideB = T.sideC := rfl
@[simp] theorem sideC_rotate (T : Triangle.{u}) : T.rotate.sideC = T.sideA := rfl
@[simp] theorem angleA_rotate (T : Triangle.{u}) : T.rotate.angleA = T.angleB := rfl
@[simp] theorem angleB_rotate (T : Triangle.{u}) : T.rotate.angleB = T.angleC := rfl
@[simp] theorem angleC_rotate (T : Triangle.{u}) : T.rotate.angleC = T.angleA := by
  change T.rotate.rotate.rotate.angleA = T.angleA
  rw [rotate_rotate_rotate]

@[simp] theorem area_rotate (T : Triangle.{u}) : T.rotate.area = T.area := by
  change |Complexify.cross (T.C - T.B) (T.A - T.B)| / 2 =
    |Complexify.cross (T.B - T.A) (T.C - T.A)| / 2
  rw [cross_triangle_cyclic]

theorem sideA_pos (T : Triangle.{u}) : 0 < T.sideA := by
  change 0 < modulus (T.B - T.C)
  rw [modulus_sub_comm]
  exact modulus_pos (left_ne_zero_of_cross_ne_zero T.rotate.noncollinear)

theorem sideB_pos (T : Triangle.{u}) : 0 < T.sideB := T.rotate.sideA_pos
theorem sideC_pos (T : Triangle.{u}) : 0 < T.sideC := T.rotate.rotate.sideA_pos
theorem area_pos (T : Triangle.{u}) : 0 < T.area :=
  triangleArea_pos_of_cross_ne_zero T.noncollinear

theorem angleA_mem (T : Triangle.{u}) :
    T.angleA.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
  interiorAngle_mem _ _ T.noncollinear

theorem sin_angleA_pos (T : Triangle.{u}) : 0 < finiteSin T.angleA :=
  finiteSin_pos_of_mem_Ioo _ T.angleA_mem

/-- The triangle's three actual finite angles sum to pi. -/
theorem angle_sum (T : Triangle.{u}) :
    T.angleA + T.angleB + T.angleC = SignSequence.finiteOfReal Real.pi :=
  interiorAngle_triangle_sum T.A T.B T.C T.noncollinear

/-- The area gives the sine of the opposite angle at every actual scale. -/
theorem sin_angleA (T : Triangle.{u}) :
    finiteSin T.angleA = 2 * T.area / (T.sideB * T.sideC) := by
  simpa only [angleA, area, sideB, sideC, modulus_sub_comm T.B T.A, mul_comm] using
    finiteSin_interiorAngle_area (T.B - T.A) (T.C - T.A) T.noncollinear

/-- The cosine law; cyclic permutation gives its other two versions. -/
theorem cosine_law (T : Triangle.{u}) :
    T.sideA ^ 2 = T.sideB ^ 2 + T.sideC ^ 2 -
      2 * T.sideB * T.sideC * finiteCos T.angleA := by
  have hd : (T.B - T.A) - (T.C - T.A) = T.B - T.C := by abel
  have he := interiorAngle_cosine_law (T.B - T.A) (T.C - T.A) T.noncollinear
  rw [hd, modulus_sub_comm T.B T.A] at he
  change T.sideA ^ 2 = T.sideC ^ 2 + T.sideB ^ 2 -
    2 * T.sideC * T.sideB * finiteCos T.angleA at he
  linear_combination he

/-- The area law; cyclic permutation gives its other two versions with the same area. -/
theorem area_law (T : Triangle.{u}) :
    T.area = T.sideB * T.sideC * finiteSin T.angleA / 2 := by
  rw [sin_angleA]
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne']

/-- The common side-to-sine ratio, before its identification with twice the circumradius. -/
theorem sine_law (T : Triangle.{u}) :
    T.sideA / finiteSin T.angleA = T.sideA * T.sideB * T.sideC / (2 * T.area) := by
  rw [sin_angleA]
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne', T.area_pos.ne']

/-- All three side-to-sine ratios coincide, including at infinite and infinitesimal scales. -/
theorem sine_law_cyclic (T : Triangle.{u}) :
    T.sideA / finiteSin T.angleA = T.sideB / finiteSin T.angleB ∧
    T.sideB / finiteSin T.angleB = T.sideC / finiteSin T.angleC := by
  have hB := T.rotate.sine_law
  have hC := T.rotate.rotate.sine_law
  simp only [sideA_rotate, sideB_rotate, sideC_rotate, angleA_rotate, angleB_rotate,
    area_rotate] at hB hC
  rw [T.sine_law, hB, hC]
  constructor <;> ring

end Triangle

/-- Positivity and the triangle angle bound keep both half-angle cosines away from zero. -/
theorem triangle_halfAngle_bounds (α β : SignSequence.FiniteElement.{u})
    (hα : 0 < α.val) (hβ : 0 < β.val) (hs : α.val + β.val < SignSequence.ofReal Real.pi) :
    (finiteHalf (α + β)).val ∈ Set.Ioo 0 (SignSequence.ofReal (Real.pi / 2)) ∧
    (finiteHalf (α - β)).val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) := by
  simp only [Set.mem_Ioo, val_finiteHalf, map_neg, map_div₀, map_ofNat]
  change (0 < (α.val + β.val) / 2 ∧
    (α.val + β.val) / 2 < SignSequence.ofReal Real.pi / 2) ∧
    (-(SignSequence.ofReal Real.pi / 2) < (α.val - β.val) / 2 ∧
    (α.val - β.val) / 2 < SignSequence.ofReal Real.pi / 2)
  constructor <;> constructor <;> linarith

/-- The tangent of the half sum in a triangle is strictly positive. -/
theorem finiteTan_half_sum_pos (α β : SignSequence.FiniteElement.{u})
    (hα : 0 < α.val) (hβ : 0 < β.val) (hs : α.val + β.val < SignSequence.ofReal Real.pi) :
    0 < finiteTan (finiteHalf (α + β)) := by
  have hi := (triangle_halfAngle_bounds α β hα hβ hs).1
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hc : 0 < finiteCos (finiteHalf (α + β)) := by
    apply finiteCos_pos_of_mem_Ioo
    simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hi ⊢
    exact ⟨by linarith [hi.1], hi.2⟩
  have hsin : 0 < finiteSin (finiteHalf (α + β)) := by
    apply finiteSin_pos_of_mem_Ioo
    rw [map_div₀, map_ofNat] at hi
    exact ⟨hi.1, by linarith [hi.2]⟩
  exact div_pos hsin hc

/-- Sum-to-product identities give the tangent ratio with all half-angle divisions justified. -/
theorem sine_ratio_eq_tangent_half_ratio (α β : SignSequence.FiniteElement.{u})
    (hα : 0 < α.val) (hβ : 0 < β.val) (hs : α.val + β.val < SignSequence.ofReal Real.pi) :
    (finiteSin α - finiteSin β) / (finiteSin α + finiteSin β) =
      finiteTan (finiteHalf (α - β)) / finiteTan (finiteHalf (α + β)) := by
  have hi := triangle_halfAngle_bounds α β hα hβ hs
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hc : 0 < finiteCos (finiteHalf (α + β)) := by
    apply finiteCos_pos_of_mem_Ioo
    simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hi ⊢
    exact ⟨by linarith [hi.1.1], hi.1.2⟩
  have hd := finiteCos_pos_of_mem_Ioo (finiteHalf (α - β)) hi.2
  have hsin : 0 < finiteSin (finiteHalf (α + β)) := by
    apply finiteSin_pos_of_mem_Ioo
    simp only [Set.mem_Ioo, map_div₀, map_ofNat] at hi
    exact ⟨hi.1.1, by linarith [hi.1.2]⟩
  rw [finiteSin_sub_finiteSin, finiteSin_add_finiteSin, finiteTan, finiteTan]
  field_simp [hc.ne', hd.ne', hsin.ne']

namespace Triangle

/-- The first two interior angles have positive sum strictly below pi. -/
theorem angleA_add_angleB_lt_pi (T : Triangle.{u}) :
    T.angleA.val + T.angleB.val < SignSequence.ofReal Real.pi := by
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) T.angle_sum
  change T.angleA.val + T.angleB.val + T.angleC.val = SignSequence.ofReal Real.pi at he
  have hp : 0 < T.angleC.val := T.rotate.rotate.angleA_mem.1
  linarith

/-- The half-sum tangent in the tangent law is a positive, hence nonzero, denominator. -/
theorem tangent_law_denominator_pos (T : Triangle.{u}) :
    0 < finiteTan (finiteHalf (T.angleA + T.angleB)) :=
  finiteTan_half_sum_pos _ _ T.angleA_mem.1 T.rotate.angleA_mem.1 T.angleA_add_angleB_lt_pi

/-- Both tangent arguments in the triangle law have strictly positive cosine denominators. -/
theorem tangent_law_cosines_pos (T : Triangle.{u}) :
    0 < finiteCos (finiteHalf (T.angleA - T.angleB)) ∧
      0 < finiteCos (finiteHalf (T.angleA + T.angleB)) := by
  have hi := triangle_halfAngle_bounds T.angleA T.angleB T.angleA_mem.1
    T.rotate.angleA_mem.1 T.angleA_add_angleB_lt_pi
  refine ⟨finiteCos_pos_of_mem_Ioo _ hi.2, ?_⟩
  apply finiteCos_pos_of_mem_Ioo
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hi ⊢
  exact ⟨by linarith [hi.1.1], hi.1.2⟩

/-- The tangent law holds for every noncollinear actual surcomplex triangle. -/
theorem tangent_law (T : Triangle.{u}) :
    (T.sideA - T.sideB) / (T.sideA + T.sideB) =
      finiteTan (finiteHalf (T.angleA - T.angleB)) /
        finiteTan (finiteHalf (T.angleA + T.angleB)) := by
  have hsinB : 0 < finiteSin T.angleB := T.rotate.sin_angleA_pos
  have he := (div_eq_div_iff T.sin_angleA_pos.ne' hsinB.ne').mp T.sine_law_cyclic.1
  calc
    _ = (finiteSin T.angleA - finiteSin T.angleB) /
        (finiteSin T.angleA + finiteSin T.angleB) := by
      apply (div_eq_div_iff (add_pos T.sideA_pos T.sideB_pos).ne'
        (add_pos T.sin_angleA_pos hsinB).ne').mpr
      nlinarith only [he]
    _ = _ := sine_ratio_eq_tangent_half_ratio _ _ T.angleA_mem.1
      T.rotate.angleA_mem.1 T.angleA_add_angleB_lt_pi

end Triangle
end
end Surreal.Surcomplex
