import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) : F.Adapted w (translate h p) := by
  apply (F.adapted_iff_coefficients w _).mpr
  intro α
  rw [coefficients_translate]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact (polynomialTranslate_monomial_bounds h w hw β).1 (MvPolynomial.mem_support_iff.mpr hc)

theorem translate_sub_coefficient_mem (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (α : σ →₀ ℕ) :
    coefficients (translate h p - p) α ∈ F.layer (Finsupp.weight w α + 1) := by
  rw [coefficients_translate_sub]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1) -
      MvPolynomial.monomial β 1).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h w hw β).2
      (MvPolynomial.mem_support_iff.mpr hc))

end Erdos3.NilpotentLieFiltration

end

end OAI
