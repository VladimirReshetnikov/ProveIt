import PolynomialFormulas.GaussianPolynomialApproximationCore
import PolynomialFormulas.GaussianPolynomialSquarefreeLayers

/-!
# Bounded separable layers for the constructive approximator

This file packages the polynomial factorization theorem into four literal
five-coefficient vectors.  Repeated irreducible factors remain in separate
layers, which is what lets the eventual output retain root multiplicities.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialApproximationFactors

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly

/-- A monic bounded quartic is a product of four monic separable bounded
polynomials, and their executable degrees add to its executable degree. -/
theorem exists_four_bounded_monic_separable_factors
    (p : QPoly4) (hp : (toPolynomial p).Monic) :
    ∃ p₀ p₁ p₂ p₃ : QPoly4,
      (toPolynomial p₀).Monic ∧ (toPolynomial p₁).Monic ∧
      (toPolynomial p₂).Monic ∧ (toPolynomial p₃).Monic ∧
      (toPolynomial p₀).Separable ∧ (toPolynomial p₁).Separable ∧
      (toPolynomial p₂).Separable ∧ (toPolynomial p₃).Separable ∧
      toPolynomial p₀ * toPolynomial p₁ * toPolynomial p₂ * toPolynomial p₃ =
        toPolynomial p ∧
      degree p₀ + degree p₁ + degree p₂ + degree p₃ = degree p := by
  obtain ⟨q₀, q₁, q₂, q₃, hm₀, hm₁, hm₂, hm₃,
      hs₀, hs₁, hs₂, hs₃, hprod, hdegree⟩ :=
    exists_four_monic_separable_factors (toPolynomial p) hp
      (natDegree_toPolynomial_le p)
  have hsumle :
      q₀.natDegree + q₁.natDegree + q₂.natDegree + q₃.natDegree ≤ 4 := by
    rw [hdegree]
    exact natDegree_toPolynomial_le p
  have hd₀ : q₀.natDegree ≤ 4 := by omega
  have hd₁ : q₁.natDegree ≤ 4 := by omega
  have hd₂ : q₂.natDegree ≤ 4 := by omega
  have hd₃ : q₃.natDegree ≤ 4 := by omega
  refine ⟨ofPolynomial 4 q₀, ofPolynomial 4 q₁,
    ofPolynomial 4 q₂, ofPolynomial 4 q₃, ?_⟩
  simp only [toPolynomial_ofPolynomial hd₀, toPolynomial_ofPolynomial hd₁,
    toPolynomial_ofPolynomial hd₂, toPolynomial_ofPolynomial hd₃]
  refine ⟨hm₀, hm₁, hm₂, hm₃, hs₀, hs₁, hs₂, hs₃, hprod, ?_⟩
  simpa only [degree_eq_natDegree, toPolynomial_ofPolynomial hd₀,
    toPolynomial_ofPolynomial hd₁, toPolynomial_ofPolynomial hd₂,
    toPolynomial_ofPolynomial hd₃] using hdegree

end GaussianPolynomialApproximationFactors

end LeanProofs.PolynomialFormulas
