import OAI.Combinatorics.Progressions.Estimates.OptionMarkedSurjective

namespace OAI

section

universe u v

namespace Erdos3

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem optionMarkedPolynomialProjection_none
    {ι : Type v} [Fintype ι] {L₀ M₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {σ : Type*} {s : ℕ} {w : σ → ℕ}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)))
    (φ : L₀ →ₗ⁅ℚ⁆ M₀) (F₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s)
    (g : ∀ i, (optionFiltrations F₀ F i).realification.PolynomialOrbit w)
    (h : VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap φ)).toLinearMap.restrictScalars ℚ) p =
        (piRealOrbit (optionFiltrations F₀ F) g).log) :
    VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map
        ((realificationLieHom (liePiEval none)).toLinearMap.restrictScalars ℚ) p) =
          (g none).log := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  erw [coefficients_map, coefficients_map]
  have hα := congrArg
    (fun q : VectorPolynomial σ ℚ
        (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace M₀ L i)) =>
      realificationLieHom (liePiEval none) (coefficients q α)) h
  simp only [coefficients_map] at hα
  change realificationLieHom (liePiEval none)
    (realificationLieHom (optionMarkedLieMap φ) (coefficients p α)) = _ at hα
  rw [realification_optionMarkedLieMap_none, piRealOrbit_coefficient] at hα
  exact hα

end Erdos3

end

end OAI
