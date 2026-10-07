import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolOfPolynomial_translate (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (translate h p) = F.realSymbolOfPolynomial b ω hF w p := by
  let q : F.realification.adaptedLieSubalgebra w :=
    ⟨p, (F.realification.mem_adaptedSubmodule w p).mpr hp⟩
  let q' : F.realification.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realification.adapted_translate w hw h hp)⟩
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hF w q' q).mpr
    (F.realification.polynomialSymbolMap_translate w hw h q)

theorem realSymbolOfPolynomial_affine (hw : ∀ i, 0 < w i) (h : σ → ℚ) (r : ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r (translate h p)) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_dilation, F.realSymbolOfPolynomial_translate b ω hF w hw h p hp]

theorem realGradedSymbolPolynomial_dilation_coefficient (r : ℚ)
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hF w (F.realPolynomialSymbolDilation w r x)) α =
      (r : ℝ) ^ Finsupp.weight w α • coefficients (F.realGradedSymbolPolynomial b ω hF w x) α := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_smul, Finsupp.smul_apply]
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), h⟩,
      F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), h⟩,
      F.realPolynomialSymbolDilation_repr]
    rfl
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i h, smul_zero]

theorem realSymbolDilation_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (r : ℚ) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    F.realPolynomialSymbolDilation w r x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w U _).mpr
  intro α
  rw [F.realGradedSymbolPolynomial_dilation_coefficient]
  exact (realificationLieSubalgebra U).smul_mem _
    ((F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w U x).mp hx α)

theorem realSymbolDilation_mem_pointwise_iff (U : LieSubalgebra ℚ F.AssociatedGraded)
    (r : ℚ) (hr : r ≠ 0) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w r x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) ↔
      x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  constructor
  · intro hx
    have h := F.realSymbolDilation_mem_pointwise b ω hF w U r⁻¹ _ hx
    simpa only [← F.realPolynomialSymbolDilation_mul, inv_mul_cancel₀ hr,
      F.realPolynomialSymbolDilation_one] using h
  · exact F.realSymbolDilation_mem_pointwise b ω hF w U r x

end Erdos3.NilpotentLieFiltration

end

end OAI
