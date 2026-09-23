import Surreal.Surcomplex.AngleDefect
import Surreal.Surcomplex.TriangleHeron
import Surreal.Surcomplex.TriangleSideValuation
import Surreal.Surcomplex.TrigonometricLeading

/-!
# Valuation geometry of actual surcomplex triangles

The exact side, area, Heron and radius identities give every valuation identity in
`trigonometry:thm:valuationtriangle` and `trigonometry:eq:valuationtriangle`. Angle defects
measure distance from either endpoint of the interior-angle interval. The final infinitesimal
angle-ratio equivalence uses finite normalized sine factors of standard part one, and therefore
places no finiteness restriction on the ratio of the sides or angles.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

local notation "v" => SignSequence.valuation

private theorem valuation_two : v (2 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using
    (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0) :
      v (SignSequence.ofReal 2 : SignSequence.{u}) = 0)

private theorem valuation_four : v (4 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using
    (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (4 : ℝ) ≠ 0) :
      v (SignSequence.ofReal 4 : SignSequence.{u}) = 0)

/-- Each actual interior sine has exactly the valuation of its angle defect. -/
theorem valuation_sin_angleA (T : Triangle.{u}) :
    v (finiteSin T.angleA) = v (angleDefect T.angleA).val :=
  valuation_finiteSin_eq_angleDefect T.angleA T.angleA_mem

/-- The sine-defect valuation identity for all three actual interior angles. -/
theorem valuation_sin_angles (T : Triangle.{u}) :
    v (finiteSin T.angleA) = v (angleDefect T.angleA).val ∧
      v (finiteSin T.angleB) = v (angleDefect T.angleB).val ∧
      v (finiteSin T.angleC) = v (angleDefect T.angleC).val :=
  ⟨T.valuation_sin_angleA, T.rotate.valuation_sin_angleA,
    T.rotate.rotate.valuation_sin_angleA⟩

/-- The ratio of two side lengths is exactly the ratio of their opposite sines. -/
theorem sideA_div_sideB_eq_sin_ratio (T : Triangle.{u}) :
    T.sideA / T.sideB = finiteSin T.angleA / finiteSin T.angleB := by
  have he := (div_eq_div_iff T.sin_angleA_pos.ne' T.rotate.sin_angleA_pos.ne').mp
    T.sine_law_cyclic.1
  apply (div_eq_div_iff T.sideB_pos.ne' T.rotate.sin_angleA_pos.ne').mpr
  simpa only [mul_comm] using he

/-- Side-valuation differences are precisely the differences of angle-defect valuations. -/
theorem valuation_side_ratio (T : Triangle.{u}) :
    v T.sideA - v T.sideB =
      v (angleDefect T.angleA).val - v (angleDefect T.angleB).val := by
  have he := congrArg v T.sideA_div_sideB_eq_sin_ratio
  simpa only [SignSequence.valuation_div, T.valuation_sin_angles.1,
    T.valuation_sin_angles.2.1] using he

/-- All three cyclic side-ratio valuation identities. -/
theorem valuation_side_ratios_cyclic (T : Triangle.{u}) :
    v T.sideA - v T.sideB =
        v (angleDefect T.angleA).val - v (angleDefect T.angleB).val ∧
      v T.sideB - v T.sideC =
        v (angleDefect T.angleB).val - v (angleDefect T.angleC).val ∧
      v T.sideC - v T.sideA =
        v (angleDefect T.angleC).val - v (angleDefect T.angleA).val := by
  refine ⟨T.valuation_side_ratio, T.rotate.valuation_side_ratio, ?_⟩
  simpa only [sideA_rotate, sideB_rotate, sideC_rotate,
    angleA_rotate, angleB_rotate, angleC_rotate] using T.rotate.rotate.valuation_side_ratio

/-- The area valuation is the sum of the two adjacent side valuations and angle defect. -/
theorem valuation_area (T : Triangle.{u}) :
    v T.area = v T.sideB + v T.sideC + v (angleDefect T.angleA).val := by
  rw [T.area_law, SignSequence.valuation_div, SignSequence.valuation_mul,
    SignSequence.valuation_mul, valuation_two, sub_zero, T.valuation_sin_angleA]

/-- The area valuation formula with each vertex in turn. -/
theorem valuation_area_cyclic (T : Triangle.{u}) :
    v T.area = v T.sideB + v T.sideC + v (angleDefect T.angleA).val ∧
      v T.area = v T.sideC + v T.sideA + v (angleDefect T.angleB).val ∧
      v T.area = v T.sideA + v T.sideB + v (angleDefect T.angleC).val := by
  refine ⟨T.valuation_area, ?_, ?_⟩
  · simpa only [area_rotate, sideB_rotate, sideC_rotate, angleA_rotate] using
      T.rotate.valuation_area
  · simpa only [area_rotate, sideA_rotate, sideB_rotate, sideC_rotate,
      angleA_rotate, angleB_rotate] using T.rotate.rotate.valuation_area

/-- Taking valuations in Heron's identity, with every semiperimeter factor positive. -/
theorem valuation_heron (T : Triangle.{u}) :
    2 • v T.area = v T.semiperimeter + v (T.semiperimeter - T.sideA) +
      v (T.semiperimeter - T.sideB) + v (T.semiperimeter - T.sideC) := by
  have he := congrArg v T.heron
  simpa only [SignSequence.valuation.map_pow, SignSequence.valuation_mul] using he

/-- The circumradius valuation has no ordinary factor-four contribution. -/
theorem valuation_circumradius (T : Triangle.{u}) :
    v T.circumradius = v T.sideA + v T.sideB + v T.sideC - v T.area := by
  rw [T.circumradius_eq_side_product, SignSequence.valuation_div,
    SignSequence.valuation_mul, SignSequence.valuation_mul,
    SignSequence.valuation_mul, valuation_four, zero_add]

/-- The inradius valuation is area valuation minus semiperimeter valuation. -/
theorem valuation_inradius (T : Triangle.{u}) :
    v T.inradius = v T.area - v T.semiperimeter := by
  rw [inradius, SignSequence.valuation_div]

/-- Ordinary doubling does not change the actual circumradius valuation. -/
theorem valuation_circumdiameter (T : Triangle.{u}) :
    v (2 * T.circumradius) = v T.circumradius := by
  rw [SignSequence.valuation_mul, valuation_two, zero_add]

/-- Side valuation minus angle-defect valuation is the circumdiameter valuation. -/
theorem valuation_side_sub_defect (T : Triangle.{u}) :
    v T.sideA - v (angleDefect T.angleA).val = v (2 * T.circumradius) := by
  have he := congrArg v T.sine_law_circumradius
  simpa only [SignSequence.valuation_div, T.valuation_sin_angleA] using he

/-- All three side-minus-defect valuations equal the same actual circumdiameter valuation. -/
theorem valuation_side_sub_defect_cyclic (T : Triangle.{u}) :
    v T.sideA - v (angleDefect T.angleA).val = v (2 * T.circumradius) ∧
      v T.sideB - v (angleDefect T.angleB).val = v (2 * T.circumradius) ∧
      v T.sideC - v (angleDefect T.angleC).val = v (2 * T.circumradius) := by
  refine ⟨T.valuation_side_sub_defect, ?_, ?_⟩
  · simpa only [sideA_rotate, angleA_rotate, circumradius_rotate] using
      T.rotate.valuation_side_sub_defect
  · simpa only [sideA_rotate, sideB_rotate, angleA_rotate, angleB_rotate,
      circumradius_rotate] using T.rotate.rotate.valuation_side_sub_defect

/-- For two infinitesimal interior angles, their ratio is algebraically equivalent to the
opposite side ratio: its normalized relative error is an actual infinitesimal. -/
theorem infinitesimal_angle_ratio_div_side_ratio_sub_one (T : Triangle.{u})
    (hA : SignSequence.IsInfinitesimal T.angleA.val)
    (hB : SignSequence.IsInfinitesimal T.angleB.val) :
    SignSequence.IsInfinitesimal
      ((T.angleA.val / T.angleB.val) / (T.sideA / T.sideB) - 1) := by
  obtain ⟨A, hAf, hAs, hAe⟩ := finiteSin_leading_factor T.angleA hA
  obtain ⟨B, hBf, hBs, hBe⟩ := finiteSin_leading_factor T.angleB hB
  have hAs0 : SignSequence.standardPart A ≠ 0 := by rw [hAs]; norm_num
  have hBs0 : SignSequence.standardPart B ≠ 0 := by rw [hBs]; norm_num
  have hA0 : A ≠ 0 := by intro h; exact hAs0 (by simp [h])
  have hB0 : B ≠ 0 := by intro h; exact hBs0 (by simp [h])
  have hAi := SignSequence.finite_inv_of_standardPart_ne_zero hAf hAs0
  have hf := SignSequence.finite_mul hBf hAi
  have hs : SignSequence.standardPart (B * A⁻¹) = 1 := by
    rw [SignSequence.standardPart_mul hBf hAi,
      SignSequence.standardPart_inv_of_ne_zero hAf hAs0, hAs, hBs]
    norm_num
  have he : (T.angleA.val / T.angleB.val) / (T.sideA / T.sideB) = B * A⁻¹ := by
    rw [T.sideA_div_sideB_eq_sin_ratio, hAe, hBe]
    have hβ0 : T.angleB.val ≠ 0 := T.rotate.angleA_mem.1.ne'
    field_simp [T.angleA_mem.1.ne', hβ0, hA0, hB0]
  rw [he]
  simpa only [hs, map_one] using SignSequence.infinitesimal_sub_standardPart hf

end
end Surreal.Surcomplex.Triangle
