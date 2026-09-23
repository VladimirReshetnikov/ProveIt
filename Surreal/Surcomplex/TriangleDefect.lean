import Surreal.Surcomplex.TriangleDefectExact
import Surreal.Surcomplex.TrigonometricLeading
import Surreal.Foundations.SignSequenceRelativeAsymptotics
import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# Quadratic asymptotics of the triangle-inequality defect

The normalized sum length has standard part one when the actual
unoriented angle is infinitesimal. Its positive denominator then gives
the exact leading factor for `trigonometry:thm:defect` and
`trigonometry:eq:defectasym`, without requiring comparable vector lengths.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem finite_four : SignSequence.IsFinite (4 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (4 : ℝ)

/-- The normalized product of two positive lengths is bounded at every relative scale. -/
theorem twice_length_product_div_sum_sq_mem (a b : SignSequence.{u})
    (ha : 0 < a) (hb : 0 < b) : 2 * a * b / (a + b) ^ 2 ∈ Set.Ioc 0 1 := by
  refine ⟨div_pos (mul_pos (mul_pos (by norm_num) ha) hb) (sq_pos_of_pos (add_pos ha hb)), ?_⟩
  apply (div_le_one (sq_pos_of_pos (add_pos ha hb))).mpr
  nlinarith only [sq_nonneg a, sq_nonneg b]

/-- The effective length scale is between half the smaller length and the smaller length. -/
theorem lengthProduct_div_sum_bounds (a b : SignSequence.{u}) (ha : 0 < a) (hb : 0 < b) :
    min a b / 2 ≤ a * b / (a + b) ∧ a * b / (a + b) < min a b := by
  have hs := add_pos ha hb
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    constructor
    · apply (le_div_iff₀ hs).mpr
      nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr h)]
    · apply (div_lt_iff₀ hs).mpr
      nlinarith only [sq_pos_of_pos ha]
  · rw [min_eq_right h]
    constructor
    · apply (le_div_iff₀ hs).mpr
      nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr h)]
    · apply (div_lt_iff₀ hs).mpr
      nlinarith only [sq_pos_of_pos hb]

/-- With an infinitesimal unoriented angle, the sum length is equivalent to the sum of lengths. -/
theorem infinitesimal_modulus_add_div_sum_sub_one (z w : Surcomplex.{u})
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hi : SignSequence.IsInfinitesimal (vectorAngle z w hz hw).val) :
    SignSequence.IsInfinitesimal (modulus (z + w) / (modulus z + modulus w) - 1) := by
  let q := modulus (z + w) / (modulus z + modulus w)
  let k := 2 * modulus z * modulus w / (modulus z + modulus w) ^ 2
  have hS : 0 < modulus z + modulus w := add_pos (modulus_pos hz) (modulus_pos hw)
  have hk := twice_length_product_div_sum_sq_mem (modulus z) (modulus w)
    (modulus_pos hz) (modulus_pos hw)
  have hkf : SignSequence.IsFinite k := by
    apply (SignSequence.isFinite_iff_exists_nat_abs_le _).mpr
    exact ⟨1, by simpa only [k, Nat.cast_one, abs_of_pos hk.1] using hk.2⟩
  have hcf := SignSequence.finite_sub SignSequence.finite_one
    (isFinite_finiteCos (vectorAngle z w hz hw))
  have hcs : SignSequence.standardPart (1 - finiteCos (vectorAngle z w hz hw)) = 0 := by
    rw [SignSequence.standardPart_sub SignSequence.finite_one (isFinite_finiteCos _),
      SignSequence.standardPart_one, standardPart_finiteCos_of_isInfinitesimal _ hi, sub_self]
  have he : q ^ 2 - 1 = -(k * (1 - finiteCos (vectorAngle z w hz hw))) := by
    dsimp only [q, k]
    rw [div_pow, modulus_add_sq_eq_vectorAngle z w hz hw]
    field_simp [hS.ne']
    ring
  apply SignSequence.infinitesimal_sub_one_of_sq_sub_one
    (div_nonneg (modulus_nonneg _) hS.le)
  rw [he]
  apply SignSequence.infinitesimal_neg
  apply (SignSequence.standardPart_eq_zero_iff (SignSequence.finite_mul hkf hcf)).mp
  rw [SignSequence.standardPart_mul hkf hcf, hcs, mul_zero]

/-- The defect has the predicted quadratic leading term times a finite factor of residue one. -/
theorem triangleDefect_leading_factor (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0)
    (hi : SignSequence.IsInfinitesimal (vectorAngle z w hz hw).val) :
    ∃ F : SignSequence.{u}, SignSequence.IsFinite F ∧ SignSequence.standardPart F = 1 ∧
      triangleDefect z w =
        (modulus z * modulus w / (2 * (modulus z + modulus w)) *
          (vectorAngle z w hz hw).val ^ 2) * F := by
  let q := modulus (z + w) / (modulus z + modulus w)
  have hq := infinitesimal_modulus_add_div_sum_sub_one z w hz hw hi
  have hqf : SignSequence.IsFinite q := SignSequence.finite_of_infinitesimal_sub_one hq
  have hqs : SignSequence.standardPart q = 1 :=
    SignSequence.standardPart_eq_one_of_infinitesimal_sub_one hq
  have hdf := SignSequence.finite_add SignSequence.finite_one hqf
  have hds : SignSequence.standardPart (1 + q) = 2 := by
    rw [SignSequence.standardPart_add SignSequence.finite_one hqf,
      SignSequence.standardPart_one, hqs]
    norm_num
  have hds0 : SignSequence.standardPart (1 + q) ≠ 0 := by rw [hds]; norm_num
  have hdif := SignSequence.finite_inv_of_standardPart_ne_zero hdf hds0
  obtain ⟨C, hCf, hCs, hCe⟩ := one_sub_finiteCos_leading_factor (vectorAngle z w hz hw) hi
  refine ⟨4 * C * (1 + q)⁻¹, SignSequence.finite_mul
    (SignSequence.finite_mul finite_four hCf) hdif, ?_, ?_⟩
  · rw [SignSequence.standardPart_mul (SignSequence.finite_mul finite_four hCf) hdif,
      SignSequence.standardPart_mul finite_four hCf,
      SignSequence.standardPart_inv_of_ne_zero hdf hds0, hCs, hds]
    have h4 : SignSequence.standardPart (4 : SignSequence.{u}) = 4 := by
      simpa only [map_ofNat] using SignSequence.standardPart_ofReal (4 : ℝ)
    rw [h4]
    norm_num
  · have hS := add_pos (modulus_pos hz) (modulus_pos hw)
    have hd : 1 + q ≠ 0 := (add_pos_of_pos_of_nonneg (by norm_num)
      (div_nonneg (modulus_nonneg _) hS.le)).ne'
    have he : modulus z + modulus w + modulus (z + w) =
        (modulus z + modulus w) * (1 + q) := by
      dsimp only [q]
      field_simp
    rw [triangleDefect_exact z w hz hw, finiteSin_finiteHalf_sq, hCe, he]
    field_simp [hS.ne', hd]

/-- The exact algebraic quadratic equivalent, with arbitrary incomparable length scales. -/
theorem triangleDefect_asymptotic (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0)
    (hi : SignSequence.IsInfinitesimal (vectorAngle z w hz hw).val)
    (hne : (vectorAngle z w hz hw).val ≠ 0) :
    SignSequence.IsInfinitesimal
      (triangleDefect z w / (modulus z * modulus w / (2 * (modulus z + modulus w)) *
        (vectorAngle z w hz hw).val ^ 2) - 1) := by
  obtain ⟨F, hFf, hFs, he⟩ := triangleDefect_leading_factor z w hz hw hi
  have hp : modulus z * modulus w / (2 * (modulus z + modulus w)) *
      (vectorAngle z w hz hw).val ^ 2 ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (modulus_pos hz).ne' (modulus_pos hw).ne')
      (mul_ne_zero (by norm_num) (add_pos (modulus_pos hz) (modulus_pos hw)).ne'))
      (pow_ne_zero _ hne)
  rw [he, mul_div_cancel_left₀ _ hp]
  simpa only [hFs, map_one] using SignSequence.infinitesimal_sub_standardPart hFf

/-- The quadratic defect's valuation records both length scales and the infinitesimal angle. -/
theorem valuation_triangleDefect (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0)
    (hi : SignSequence.IsInfinitesimal (vectorAngle z w hz hw).val) :
    SignSequence.valuation (triangleDefect z w) =
      SignSequence.valuation (modulus z) + SignSequence.valuation (modulus w) +
        2 • SignSequence.valuation (vectorAngle z w hz hw).val -
          SignSequence.valuation (modulus z + modulus w) := by
  obtain ⟨F, hFf, hFs, he⟩ := triangleDefect_leading_factor z w hz hw hi
  have hvF := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hFf).mpr
    (by rw [hFs]; norm_num)
  have hv2 : SignSequence.valuation (2 : SignSequence.{u}) = 0 := by
    simpa only [map_ofNat] using
      (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0) :
        SignSequence.valuation (SignSequence.ofReal 2 : SignSequence.{u}) = 0)
  rw [he, SignSequence.valuation_mul, SignSequence.valuation_mul,
    SignSequence.valuation_div, SignSequence.valuation_mul, SignSequence.valuation_mul,
    hv2, zero_add, hvF, add_zero, SignSequence.valuation.map_pow]
  simp only [sub_eq_add_neg]
  ac_rfl

end
end Surreal.Surcomplex
