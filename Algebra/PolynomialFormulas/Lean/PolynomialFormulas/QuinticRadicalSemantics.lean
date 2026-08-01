import PolynomialFormulas.QuinticRadicalDecidability
import PolynomialFormulas.QuinticRadicalComputability
import PolynomialFormulas.ReducibleQuinticRadicals

/-!
# Semantic reductions for integer quintics

This module connects the executable six-integer representation to the monic
integer quintic used by the bounded factor search.  The monicization
`F(a₅ x) = a₅⁴ f(x)` preserves membership of every complex root in the
radical closure.  It also discharges the reducible branch of the eventual
quintic decision procedure by reducing all proper factors to degree at most
four.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.QuinticRadicalSemantics

noncomputable def monicRatPolynomial
    (a : QuinticRadicalComputability.Coefficients) : ℚ[X] :=
  (QuinticRadicalDecidability.monicize a).polynomial.map (Int.castRingHom ℚ)

theorem intPolynomial_eq (a : QuinticRadicalComputability.Coefficients) :
    QuinticRadicalComputability.intPolynomial a =
      QuinticRadicalDecidability.IntegerQuintic.polynomial a := by
  rfl

theorem monicize_aeval_scale
    (a : QuinticRadicalComputability.Coefficients) (x : ℂ) :
    (monicRatPolynomial a).aeval ((a 5 : ℂ) * x) =
      (a 5 : ℂ) ^ 4 *
        (QuinticRadicalComputability.ratPolynomial a).aeval x := by
  simp [monicRatPolynomial,
    QuinticRadicalDecidability.MonicQuintic.polynomial,
    QuinticRadicalDecidability.monicize,
    QuinticRadicalComputability.ratPolynomial,
    QuinticRadicalComputability.intPolynomial,
    QuinticRadicalDecidability.IntegerQuintic.polynomial]
  ring

theorem monicRatPolynomial_monic
    (a : QuinticRadicalComputability.Coefficients) :
    (monicRatPolynomial a).Monic := by
  exact (QuinticRadicalDecidability.monicize a).polynomial_monic.map
    (Int.castRingHom ℚ)

@[simp] theorem monicRatPolynomial_natDegree
    (a : QuinticRadicalComputability.Coefficients) :
    (monicRatPolynomial a).natDegree = 5 := by
  rw [monicRatPolynomial,
    (QuinticRadicalDecidability.monicize a).polynomial_monic.natDegree_map]
  exact (QuinticRadicalDecidability.monicize a).polynomial_natDegree

theorem hasBoundedProperFactor_iff_monicRatPolynomial_not_irreducible
    (a : QuinticRadicalComputability.Coefficients) :
    (QuinticRadicalDecidability.monicize a).hasBoundedProperFactor = true ↔
      ¬Irreducible (monicRatPolynomial a) := by
  simpa [monicRatPolynomial] using
    QuinticRadicalDecidability.MonicQuintic.hasBoundedProperFactor_iff_not_irreducible_map_rat
        (QuinticRadicalDecidability.monicize a)

theorem ratPolynomial_natDegree
    (a : QuinticRadicalComputability.Coefficients) (ha : a 5 ≠ 0) :
    (QuinticRadicalComputability.ratPolynomial a).natDegree = 5 := by
  rw [QuinticRadicalComputability.ratPolynomial, intPolynomial_eq]
  calc
    ((QuinticRadicalDecidability.IntegerQuintic.polynomial a).map
        (Int.castRingHom ℚ)).natDegree =
        (QuinticRadicalDecidability.IntegerQuintic.polynomial a).natDegree :=
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective
        (QuinticRadicalDecidability.IntegerQuintic.polynomial a)
    _ = 5 :=
      QuinticRadicalDecidability.IntegerQuintic.natDegree_eq_five a ha

theorem completelySolvableByRadicals_monicize_iff
    (a : QuinticRadicalComputability.Coefficients) (ha : a 5 ≠ 0) :
    CompletelySolvableByRadicals (monicRatPolynomial a) ↔
      CompletelySolvableByRadicals
        (QuinticRadicalComputability.ratPolynomial a) := by
  have haC : (a 5 : ℂ) ≠ 0 := by exact_mod_cast ha
  have hmonic0 : monicRatPolynomial a ≠ 0 :=
    (monicRatPolynomial_monic a).ne_zero
  have horig0 : QuinticRadicalComputability.ratPolynomial a ≠ 0 := by
    intro hzero
    have hdeg := ratPolynomial_natDegree a ha
    rw [hzero, natDegree_zero] at hdeg
    norm_num at hdeg
  constructor
  · intro h x
    let y : (monicRatPolynomial a).rootSet ℂ :=
      ⟨(a 5 : ℂ) * (x : ℂ), (mem_rootSet_of_ne hmonic0).2 (by
        rw [monicize_aeval_scale,
          aeval_eq_zero_of_mem_rootSet x.property, mul_zero])⟩
    have hy := h y
    have heq : (x : ℂ) = (y : ℂ) / (a 5 : ℂ) := by
      dsimp [y]
      field_simp
    rw [heq]
    exact div_mem hy (IntermediateField.algebraMap_mem _ (a 5 : ℚ))
  · intro h y
    let x : (QuinticRadicalComputability.ratPolynomial a).rootSet ℂ :=
      ⟨(y : ℂ) / (a 5 : ℂ), (mem_rootSet_of_ne horig0).2 (by
        have hscale := monicize_aeval_scale a ((y : ℂ) / (a 5 : ℂ))
        have hyScale :
            (a 5 : ℂ) * ((y : ℂ) / (a 5 : ℂ)) = (y : ℂ) := by
          field_simp
        rw [hyScale, aeval_eq_zero_of_mem_rootSet y.property] at hscale
        exact (mul_eq_zero.mp hscale.symm).resolve_left
          (pow_ne_zero 4 haC))⟩
    have hx := h x
    have heq : (y : ℂ) = (a 5 : ℂ) * (x : ℂ) := by
      dsimp [x]
      field_simp
    rw [heq]
    exact mul_mem (IntermediateField.algebraMap_mem _ (a 5 : ℚ)) hx

theorem allRootsRadical_of_monicize_not_irreducible
    (a : QuinticRadicalComputability.Coefficients) (ha : a 5 ≠ 0)
    (hred : ¬Irreducible (monicRatPolynomial a)) :
    QuinticRadicalComputability.AllRootsRadical a := by
  refine ⟨ha, (completelySolvableByRadicals_monicize_iff a ha).mp ?_⟩
  exact
    ReducibleQuinticRadicals.completelySolvableByRadicals_of_monic_natDegree_five_not_irreducible
      (monicRatPolynomial_monic a) (monicRatPolynomial_natDegree a) hred

end LeanProofs.PolynomialFormulas.QuinticRadicalSemantics
