import Surreal.Algebra.IntersectiveDetector
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Analysis.Real.Sqrt

/-!
# The augmentation detector with a zero-divisor input

The explicit R × R example following `odg:def:thm:augdetector`.
First projection is the augmentation, its integer pullback is Z × R,
and (1,0) has the printed certificate despite being a zero divisor.
-/

namespace Surreal.AugmentationRootDetector

noncomputable section

/-- The diagonal real algebra with augmentation given by first projection. -/
abbrev productAugmentation : (ℝ × ℝ) →ₐ[ℝ] ℝ := AlgHom.fst ℝ ℝ ℝ

/-- Its integer pullback is precisely the pairs with an integer first coordinate. -/
theorem product_pullback_iff (x : ℝ × ℝ) :
    x ∈ CoefficientPullback.subring productAugmentation.toRingHom (Int.castRingHom ℝ) ↔
      ∃ n : ℤ, x.1 = n := by
  change (∃ n : ℤ, (n : ℝ) = x.1) ↔ _
  exact exists_congr (fun _ => eq_comm)

/-- The input (1,0) is nonzero and annihilates the nonzero element (0,1). -/
theorem product_input_zero_divisor :
    ((1, 0) : ℝ × ℝ) ≠ 0 ∧ ((0, 1) : ℝ × ℝ) ≠ 0 ∧
      ((1, 0) : ℝ × ℝ) * (0, 1) = 0 := by
  norm_num [Prod.mk_mul_mk]

/-- The displayed witnesses solve the equation and lie in the integer pullback. -/
theorem product_input_certificate :
    ((1, 0) : ℝ × ℝ) * (-48841, 0) = IntersectivePolynomial.value (0, Real.sqrt 13) ∧
      ((-48841, 0) : ℝ × ℝ) ∈
        CoefficientPullback.subring productAugmentation.toRingHom (Int.castRingHom ℝ) ∧
      (0, Real.sqrt 13) ∈
        CoefficientPullback.subring productAugmentation.toRingHom (Int.castRingHom ℝ) := by
  refine ⟨?_, (product_pullback_iff _).mpr ⟨-48841, by norm_num⟩,
    (product_pullback_iff _).mpr ⟨0, by simp⟩⟩
  ext <;> norm_num [IntersectivePolynomial.value, Real.sq_sqrt]

end
end Surreal.AugmentationRootDetector
