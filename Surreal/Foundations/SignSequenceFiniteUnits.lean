import Surreal.Foundations.SignSequenceValuation

/-!
# Inverting finite actual surreals with nonzero standard part

These elementary residue and valuation rules support algebraic asymptotics,
including the tangent quotient in `trigonometry:prop:leading`.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- On finite elements, valuation zero is equivalent to a nonzero residue. -/
theorem valuation_eq_zero_iff_standardPart_ne_zero {x : SignSequence.{u}} (hx : IsFinite x) :
    valuation x = 0 ↔ standardPart x ≠ 0 := by
  rw [ne_eq, standardPart_eq_zero_iff hx, isInfinitesimal_iff_valuation_pos, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h ((isFinite_iff_valuation_nonneg x).mp hx)⟩

/-- A nonzero standard part makes a finite element's reciprocal finite. -/
theorem finite_inv_of_standardPart_ne_zero {x : SignSequence.{u}}
    (hx : IsFinite x) (hstd : standardPart x ≠ 0) : IsFinite x⁻¹ := by
  rw [isFinite_iff_valuation_nonneg, valuation_inv,
    (valuation_eq_zero_iff_standardPart_ne_zero hx).mpr hstd, neg_zero]

/-- Standard part commutes with inversion on the units of the finite ring. -/
theorem standardPart_inv_of_ne_zero {x : SignSequence.{u}}
    (hx : IsFinite x) (hstd : standardPart x ≠ 0) : standardPart x⁻¹ = (standardPart x)⁻¹ := by
  have hne : x ≠ 0 := by intro h; exact hstd (by simp [h])
  have h := standardPart_mul hx (finite_inv_of_standardPart_ne_zero hx hstd)
  rw [mul_inv_cancel₀ hne, standardPart_one] at h
  apply mul_left_cancel₀ hstd
  rw [mul_inv_cancel₀ hstd]
  exact h.symm

/-- Every natural power of a finite actual surreal remains finite. -/
theorem finite_pow {x : SignSequence.{u}} (hx : IsFinite x) (n : ℕ) : IsFinite (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using finite_one
  | succ n ih => simpa only [pow_succ] using finite_mul ih hx

end Surreal.Foundations.SignSequence
