import PolynomialFormulas.SexticRadicalComputability

/-!
# Semantic monicization for integer sextics

Scaling roots by the nonzero leading coefficient identifies the original
integer sextic with its integral monicization.  This file proves that the
identification preserves the exact all-roots radical-solvability predicate.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.SexticRadicalSemantics

open LeanProofs.PolynomialFormulas
open SexticRadicalDecidability

noncomputable def monicRatPolynomial (a : Coefficients) : ℚ[X] :=
  (monicize a).ratPolynomial

theorem monicize_aeval_scale (a : Coefficients) (x : ℂ) :
    (monicRatPolynomial a).aeval ((a 6 : ℂ) * x) =
      (a 6 : ℂ) ^ 5 * a.ratPolynomial.aeval x := by
  simp [monicRatPolynomial, MonicSextic.ratPolynomial,
    MonicSextic.polynomial, monicize, Coefficients.ratPolynomial,
    QuinticRadicalDecidability.IntegerSextic.polynomial]
  ring

theorem monicRatPolynomial_monic (a : Coefficients) :
    (monicRatPolynomial a).Monic := by
  exact (monicize a).ratPolynomial_monic

@[simp] theorem monicRatPolynomial_natDegree (a : Coefficients) :
    (monicRatPolynomial a).natDegree = 6 := by
  exact (monicize a).ratPolynomial_natDegree

theorem ratPolynomial_natDegree (a : Coefficients) (ha : a.IsSextic) :
    a.ratPolynomial.natDegree = 6 :=
  a.ratPolynomial_natDegree_eq_six ha

/-- Multiplying or dividing a root by the rational leading coefficient stays
inside the radical closure, so monicization preserves all-root solvability. -/
theorem completelySolvableByRadicals_monicize_iff
    (a : Coefficients) (ha : a.IsSextic) :
    CompletelySolvableByRadicals (monicRatPolynomial a) ↔
      CompletelySolvableByRadicals a.ratPolynomial := by
  have haC : (a 6 : ℂ) ≠ 0 := by exact_mod_cast ha
  have hmonic0 : monicRatPolynomial a ≠ 0 :=
    (monicRatPolynomial_monic a).ne_zero
  have horig0 : a.ratPolynomial ≠ 0 := by
    intro hzero
    have hdeg := ratPolynomial_natDegree a ha
    rw [hzero, natDegree_zero] at hdeg
    norm_num at hdeg
  constructor
  · intro h x
    let y : (monicRatPolynomial a).rootSet ℂ :=
      ⟨(a 6 : ℂ) * (x : ℂ), (mem_rootSet_of_ne hmonic0).2 (by
        rw [monicize_aeval_scale,
          aeval_eq_zero_of_mem_rootSet x.property, mul_zero])⟩
    have hy := h y
    have heq : (x : ℂ) = (y : ℂ) / (a 6 : ℂ) := by
      dsimp [y]
      field_simp
    rw [heq]
    exact div_mem hy (IntermediateField.algebraMap_mem _ (a 6 : ℚ))
  · intro h y
    let x : a.ratPolynomial.rootSet ℂ :=
      ⟨(y : ℂ) / (a 6 : ℂ), (mem_rootSet_of_ne horig0).2 (by
        have hscale := monicize_aeval_scale a ((y : ℂ) / (a 6 : ℂ))
        have hyScale :
            (a 6 : ℂ) * ((y : ℂ) / (a 6 : ℂ)) = (y : ℂ) := by
          field_simp
        rw [hyScale, aeval_eq_zero_of_mem_rootSet y.property] at hscale
        exact (mul_eq_zero.mp hscale.symm).resolve_left
          (pow_ne_zero 5 haC))⟩
    have hx := h x
    have heq : (y : ℂ) = (a 6 : ℂ) * (x : ℂ) := by
      dsimp [x]
      field_simp
    rw [heq]
    exact mul_mem (IntermediateField.algebraMap_mem _ (a 6 : ℚ)) hx

end LeanProofs.PolynomialFormulas.SexticRadicalSemantics
