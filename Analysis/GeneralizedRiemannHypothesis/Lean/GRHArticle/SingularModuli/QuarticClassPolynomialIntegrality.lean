import GRHArticle.SingularModuli.CMHeckeIntegralDiagonal
import GRHArticle.SingularModuli.QuarticClassPolynomialCertificates
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Algebraic-integral coefficients of the two analytic CM quartics

The root certificates for the integer Hecke diagonals give algebraic
integrality of every coefficient. Rationality of the coefficients would
therefore suffice for the printed identities and the support bounds.
-/

namespace GRHArticle.SingularModuli

open Polynomial

private theorem isIntegral_coeff_analyticClassPolynomial (D : ℕ+)
    (h : ∀ f ∈ reducedForms D,
      IsIntegral ℤ (modularInvariant (quadraticPoint D f.a f.b))) (i : ℕ) :
    IsIntegral ℤ ((analyticClassPolynomial D).coeff i) := by
  unfold analyticClassPolynomial
  refine Polynomial.isIntegral_coeff_prod _ _ (fun f hf n ↦ ?_) i
  rw [coeff_sub, coeff_X, coeff_C]
  apply IsIntegral.sub
  · split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  · split_ifs
    · exact h f hf
    · exact isIntegral_zero

/-- Every complex coefficient of the discriminant `-55` analytic quartic
is an algebraic integer. -/
theorem analyticClassPolynomial_fiftyFive_coeff_isIntegral (i : ℕ) :
    IsIntegral ℤ ((analyticClassPolynomial 55).coeff i) := by
  apply isIntegral_coeff_analyticClassPolynomial
  intro f hf
  rw [reducedForms_fiftyFive] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact quartic55_singularModulus_isIntegral 0
  · exact quartic55_singularModulus_isIntegral 1
  · exact quartic55_singularModulus_isIntegral 2
  · exact quartic55_singularModulus_isIntegral 3

/-- Every complex coefficient of the discriminant `-68` analytic quartic
is an algebraic integer. -/
theorem analyticClassPolynomial_sixtyEight_coeff_isIntegral (i : ℕ) :
    IsIntegral ℤ ((analyticClassPolynomial 68).coeff i) := by
  apply isIntegral_coeff_analyticClassPolynomial
  intro f hf
  rw [reducedForms_sixtyEight] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact quartic68_singularModulus_isIntegral 0
  · exact quartic68_singularModulus_isIntegral 1
  · exact quartic68_singularModulus_isIntegral 2
  · exact quartic68_singularModulus_isIntegral 3

private theorem exists_int_of_isIntegral_of_ratCast {z : ℂ}
    (h : IsIntegral ℤ z) (hr : ∃ r : ℚ, z = (r : ℂ)) : ∃ k : ℤ, z = (k : ℂ) := by
  obtain ⟨r, rfl⟩ := hr
  change IsIntegral ℤ (algebraMap ℚ ℂ r) at h
  have h' := (isIntegral_algebraMap_iff (R := ℤ) (algebraMap ℚ ℂ).injective).mp h
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  change (k : ℚ) = r at hk
  exact ⟨k, by rw [← hk, Rat.cast_intCast]⟩

theorem analyticClassPolynomial_fiftyFive_eq_printed_of_rational
    (h : ∀ n : Fin 5, ∃ r : ℚ, (analyticClassPolynomial 55).coeff n = (r : ℂ)) :
    analyticClassPolynomial 55 = quartic55Int.map (Int.castRingHom ℂ) :=
  analyticClassPolynomial_fiftyFive_eq_printed_of_integral fun n ↦
    exists_int_of_isIntegral_of_ratCast (analyticClassPolynomial_fiftyFive_coeff_isIntegral n) (h n)

theorem analyticClassPolynomial_sixtyEight_eq_printed_of_rational
    (h : ∀ n : Fin 5, ∃ r : ℚ, (analyticClassPolynomial 68).coeff n = (r : ℂ)) :
    analyticClassPolynomial 68 = quartic68Int.map (Int.castRingHom ℂ) :=
  analyticClassPolynomial_sixtyEight_eq_printed_of_integral fun n ↦
    exists_int_of_isIntegral_of_ratCast (analyticClassPolynomial_sixtyEight_coeff_isIntegral n) (h n)

end GRHArticle.SingularModuli
