import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop

namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolMap_basis_independent
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w p = F.realPolynomialSymbolMap c ν hC w p := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x) =
    F.realSymbolOfPolynomial c ν hC w (F.realAdaptedPolynomialMap w x)
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

theorem realPolynomialSymbolHom_basis_independent
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF w g = F.realPolynomialSymbolHom c ν hC w g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolynomialSymbolMap_basis_independent b ω hF c ν hC w g.coord

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d e : ℕ} {σ ι κ : Type*} {w : σ → ℕ}

theorem pairOrbitSymbol_basis_independent
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (c : Basis κ ℚ (PairAlgebra L M)) (ν : κ → ℕ)
    (hC : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (c '' {i | k ≤ ν i})) :
    pairOrbitSymbol D E p q b ω hF = pairOrbitSymbol D E p q c ν hC :=
  (pi (pairModels D E)).filtration.realPolynomialSymbolHom_basis_independent
    b ω hF c ν hC w _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
