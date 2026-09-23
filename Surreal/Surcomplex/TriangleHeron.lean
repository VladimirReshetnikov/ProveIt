import Surreal.Surcomplex.TriangleSideData

/-!
# Heron's formula and positive half-angle formulas

Package the semiperimeter and its positive side defects for actual
noncollinear triangles. Heron's identity and the cosine law prove the
positive square-root formulas in `trigonometry:thm:heron` and
`trigonometry:eq:halfangletriangle`. The ratio of area to semiperimeter
is defined here; its geometric identification as the incircle radius is
proved separately.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- Half the sum of the three actual side lengths. -/
def semiperimeter (T : Triangle.{u}) : SignSequence.{u} :=
  (T.sideA + T.sideB + T.sideC) / 2

@[simp] theorem semiperimeter_rotate (T : Triangle.{u}) :
    T.rotate.semiperimeter = T.semiperimeter := by
  simp only [semiperimeter, sideA_rotate, sideB_rotate, sideC_rotate]
  ring

theorem semiperimeter_pos (T : Triangle.{u}) : 0 < T.semiperimeter :=
  div_pos (add_pos (add_pos T.sideA_pos T.sideB_pos) T.sideC_pos) (by norm_num)

/-- Strict triangle inequalities make all three side defects positive. -/
theorem semiperimeter_sub_sideA_pos (T : Triangle.{u}) :
    0 < T.semiperimeter - T.sideA := by
  dsimp [semiperimeter]
  linarith [T.sideA_lt_add]

theorem semiperimeter_sub_sideB_pos (T : Triangle.{u}) :
    0 < T.semiperimeter - T.sideB := by
  simpa only [semiperimeter_rotate, sideA_rotate] using
    T.rotate.semiperimeter_sub_sideA_pos

theorem semiperimeter_sub_sideC_pos (T : Triangle.{u}) :
    0 < T.semiperimeter - T.sideC := by
  simpa only [semiperimeter_rotate, sideA_rotate, sideB_rotate] using
    T.rotate.rotate.semiperimeter_sub_sideA_pos

/-- Heron's formula for an arbitrary actual noncollinear triangle. -/
theorem heron (T : Triangle.{u}) :
    T.area ^ 2 = T.semiperimeter * (T.semiperimeter - T.sideA) *
      (T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC) := by
  have hd : (T.B - T.A) - (T.C - T.A) = T.B - T.C := by abel
  simpa only [hd, modulus_sub_comm T.B T.A, area, semiperimeter, sideA, sideB, sideC]
    using Surcomplex.heron (T.B - T.A) (T.C - T.A)

/-- The positive area-to-semiperimeter ratio, geometrically identified by the incircle proof. -/
def inradius (T : Triangle.{u}) : SignSequence.{u} := T.area / T.semiperimeter

theorem inradius_pos (T : Triangle.{u}) : 0 < T.inradius :=
  div_pos T.area_pos T.semiperimeter_pos

@[simp] theorem inradius_rotate (T : Triangle.{u}) : T.rotate.inradius = T.inradius := by
  simp only [inradius, area_rotate, semiperimeter_rotate]

/-- Each interior half-angle lies in the positive open quadrant. -/
theorem half_angleA_mem (T : Triangle.{u}) :
    (finiteHalf T.angleA).val ∈ Set.Ioo 0 (SignSequence.ofReal (Real.pi / 2)) := by
  rw [val_finiteHalf, map_div₀, map_ofNat]
  exact ⟨div_pos T.angleA_mem.1 (by norm_num),
    div_lt_div_of_pos_right T.angleA_mem.2 (by norm_num)⟩

theorem sin_half_angleA_pos (T : Triangle.{u}) : 0 < finiteSin (finiteHalf T.angleA) := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hi := T.half_angleA_mem
  rw [map_div₀, map_ofNat] at hi
  exact finiteSin_pos_of_mem_Ioo _ ⟨hi.1, by linarith [hi.2]⟩

theorem cos_half_angleA_pos (T : Triangle.{u}) : 0 < finiteCos (finiteHalf T.angleA) := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hi := T.half_angleA_mem
  apply finiteCos_pos_of_mem_Ioo
  simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hi ⊢
  exact ⟨by linarith [hi.1], hi.2⟩

theorem tan_half_angleA_pos (T : Triangle.{u}) : 0 < finiteTan (finiteHalf T.angleA) :=
  div_pos T.sin_half_angleA_pos T.cos_half_angleA_pos

/-- The half-angle sine square is determined by the two opposite side defects. -/
theorem sin_half_angleA_sq (T : Triangle.{u}) :
    finiteSin (finiteHalf T.angleA) ^ 2 =
      (T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC) /
        (T.sideB * T.sideC) := by
  have hd := finiteCos_two_mul (finiteHalf T.angleA)
  rw [two_mul_finiteHalf] at hd
  have hs := finiteCos_sq_add_finiteSin_sq (finiteHalf T.angleA)
  have he : finiteSin (finiteHalf T.angleA) ^ 2 = (1 - finiteCos T.angleA) / 2 := by
    linarith only [hd, hs]
  rw [he, T.cos_angleA_eq_side_quotient]
  dsimp [semiperimeter]
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne']
  ring

/-- The half-angle cosine square is determined by the semiperimeter and adjacent defect. -/
theorem cos_half_angleA_sq (T : Triangle.{u}) :
    finiteCos (finiteHalf T.angleA) ^ 2 =
      T.semiperimeter * (T.semiperimeter - T.sideA) / (T.sideB * T.sideC) := by
  have hd := finiteCos_two_mul (finiteHalf T.angleA)
  rw [two_mul_finiteHalf] at hd
  have hs := finiteCos_sq_add_finiteSin_sq (finiteHalf T.angleA)
  have he : finiteCos (finiteHalf T.angleA) ^ 2 = (1 + finiteCos T.angleA) / 2 := by
    linarith only [hd, hs]
  rw [he, T.cos_angleA_eq_side_quotient]
  dsimp [semiperimeter]
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne']
  ring

/-- Positivity selects the positive square root for the half-angle sine. -/
theorem sin_half_angleA (T : Triangle.{u}) :
    finiteSin (finiteHalf T.angleA) = SignSequence.sqrt
      ((T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC) /
        (T.sideB * T.sideC)) :=
  (SignSequence.sqrt_eq_of_nonneg_sq T.sin_half_angleA_pos.le T.sin_half_angleA_sq).symm

/-- Positivity selects the positive square root for the half-angle cosine. -/
theorem cos_half_angleA (T : Triangle.{u}) :
    finiteCos (finiteHalf T.angleA) = SignSequence.sqrt
      (T.semiperimeter * (T.semiperimeter - T.sideA) / (T.sideB * T.sideC)) :=
  (SignSequence.sqrt_eq_of_nonneg_sq T.cos_half_angleA_pos.le T.cos_half_angleA_sq).symm

theorem tan_half_angleA_sq (T : Triangle.{u}) :
    finiteTan (finiteHalf T.angleA) ^ 2 =
      (T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC) /
        (T.semiperimeter * (T.semiperimeter - T.sideA)) := by
  rw [finiteTan, div_pow, T.sin_half_angleA_sq, T.cos_half_angleA_sq]
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne', T.semiperimeter_pos.ne',
    T.semiperimeter_sub_sideA_pos.ne']

/-- The half-angle tangent is the positive root of the defect ratio. -/
theorem tan_half_angleA (T : Triangle.{u}) :
    finiteTan (finiteHalf T.angleA) = SignSequence.sqrt
      ((T.semiperimeter - T.sideB) * (T.semiperimeter - T.sideC) /
        (T.semiperimeter * (T.semiperimeter - T.sideA))) :=
  (SignSequence.sqrt_eq_of_nonneg_sq T.tan_half_angleA_pos.le T.tan_half_angleA_sq).symm

/-- Heron's identity identifies the tangent ratio with the area-to-semiperimeter radius. -/
theorem tan_half_angleA_eq_inradius (T : Triangle.{u}) :
    finiteTan (finiteHalf T.angleA) = T.inradius / (T.semiperimeter - T.sideA) := by
  apply (sq_eq_sq₀ T.tan_half_angleA_pos.le
    (div_pos T.inradius_pos T.semiperimeter_sub_sideA_pos).le).mp
  rw [T.tan_half_angleA_sq, inradius, div_pow, div_pow, T.heron]
  field_simp [T.semiperimeter_pos.ne', T.semiperimeter_sub_sideA_pos.ne']

end
end Surreal.Surcomplex.Triangle
