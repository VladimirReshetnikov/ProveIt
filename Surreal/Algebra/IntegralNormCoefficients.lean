import Surreal.Algebra.SeparableNormFactors
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Integral coefficients of a number-field norm form

The last assertion of `odg:thm:norm`. A rational basis of algebraic
integers need not be an integral basis or be closed under multiplication.
The complex embedding factorization puts all coefficients in the integral
closure of Z; rational algebraic integers are then ordinary integers.
-/

namespace Surreal.NormForm

open Module MvPolynomial

noncomputable section

variable {L ι : Type*} [Field L] [Algebra ℚ L] [Module.Finite ℚ L]
  [Fintype ι] [DecidableEq ι]

/-- Integral basis elements give integral rational coefficients in the norm polynomial. -/
theorem coefficient_isIntegral (b : Basis ι ℚ L) (hb : ∀ j, IsIntegral ℤ (b j)) (m : ι →₀ ℕ) :
    IsIntegral ℤ ((polynomial b).coeff m) := by
  classical
  let g (σ : L →ₐ[ℚ] ℂ) (j : ι) : integralClosure ℤ ℂ :=
    ⟨σ (b j), map_isIntegral_int σ (hb j)⟩
  let P : MvPolynomial ι (integralClosure ℤ ℂ) := ∏ σ : L →ₐ[ℚ] ℂ, ∑ j, C (g σ j) * X j
  let φ : integralClosure ℤ ℂ →+* ℂ := (integralClosure ℤ ℂ).val.toRingHom
  have hp : (polynomial b).map (algebraMap ℚ ℂ) = P.map φ := by
    rw [polynomial_map_eq_prod]
    simp [P, g, φ]
  have he := congrArg (MvPolynomial.coeff m) hp
  simp only [coeff_map] at he
  apply (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp
  rw [he]
  exact (P.coeff m).property

/-- Each norm coefficient is an ordinary integer, without assuming an integral basis. -/
theorem coefficient_eq_int (b : Basis ι ℚ L) (hb : ∀ j, IsIntegral ℤ (b j)) (m : ι →₀ ℕ) :
    ∃ z : ℤ, (z : ℚ) = (polynomial b).coeff m :=
  IsIntegrallyClosed.isIntegral_iff.mp (coefficient_isIntegral b hb m)

/-- The entire rational norm form descends to a native polynomial with integer coefficients. -/
theorem exists_integer_polynomial (b : Basis ι ℚ L) (hb : ∀ j, IsIntegral ℤ (b j)) :
    ∃ P : MvPolynomial ι ℤ, P.map (Int.castRingHom ℚ) = polynomial b := by
  classical
  apply mem_range_map_iff_coeffs_subset.mpr
  intro r hr
  obtain ⟨m, _, rfl⟩ := mem_coeffs_iff.mp hr
  exact coefficient_eq_int b hb m

end
end Surreal.NormForm
