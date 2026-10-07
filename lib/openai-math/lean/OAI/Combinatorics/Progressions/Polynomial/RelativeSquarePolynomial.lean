import OAI.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

noncomputable def normalizedRelativeSubmodule : Submodule ℚ (F.adaptedLieSubalgebra w) :=
  (F.shiftedAdaptedIdeal w).toSubmodule ⊓ (F.layer 2).comap (F.adaptedCoefficientMap w 0)

include hw in
theorem normalizedRelative_coefficient_mem_two (p : F.normalizedRelativeSubmodule w) (α : σ →₀ ℕ) :
    coefficients p.val.val α ∈ F.layer 2 := by
  by_cases hα : α = 0
  · subst α
    exact p.property.2
  · exact F.antitone (by have := positive_weight_of_ne_zero w hw hα; omega) (p.property.1 α)

noncomputable def relativeSquarePolynomial (p : F.normalizedRelativeSubmodule w) :
    VectorPolynomial σ ℚ F.squareLieSubalgebra :=
  restrictCoefficients F.squareLieSubalgebra.toSubmodule (pair p.val.val 0) (by
    intro α
    rw [coefficients_pair, map_zero, Finsupp.zero_apply]
    apply (F.mem_squareLieSubalgebra _).mpr
    simpa only [sub_zero] using F.normalizedRelative_coefficient_mem_two w hw p α)

theorem relativeSquarePolynomial_coefficient (p : F.normalizedRelativeSubmodule w) (α : σ →₀ ℕ) :
    (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) = (coefficients p.val.val α, 0) := by
  rw [relativeSquarePolynomial, coefficients_restrictCoefficients, coefficients_pair, map_zero,
    Finsupp.zero_apply]

theorem relativeSquarePolynomial_adapted (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquarePolynomial w hw p ∈ F.squareFiltration.adaptedLieSubalgebra w := by
  intro α
  change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈ F.squareLayer (Finsupp.weight w α)
  rw [F.relativeSquarePolynomial_coefficient]
  refine ⟨p.val.property α, (F.layer _).zero_mem, ?_⟩
  change coefficients p.val.val α - 0 ∈ F.layer (Finsupp.weight w α + 1)
  rw [sub_zero]
  exact p.property.1 α

noncomputable def relativeSquareLift :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.adaptedLieSubalgebra w where
  toFun p := ⟨F.relativeSquarePolynomial w hw p, F.relativeSquarePolynomial_adapted w hw p⟩
  map_add' p q := by
    apply Subtype.ext
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    change coefficients (F.relativeSquarePolynomial w hw (p + q)) α =
      coefficients (F.relativeSquarePolynomial w hw p + F.relativeSquarePolynomial w hw q) α
    rw [map_add, Finsupp.add_apply]
    apply Subtype.ext
    change (coefficients (F.relativeSquarePolynomial w hw (p + q)) α : L × L) =
      (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) +
        (coefficients (F.relativeSquarePolynomial w hw q) α : L × L)
    rw [F.relativeSquarePolynomial_coefficient, F.relativeSquarePolynomial_coefficient,
      F.relativeSquarePolynomial_coefficient]
    change (coefficients (p.val.val + q.val.val) α, 0) = _
    simp only [map_add, Finsupp.add_apply, Prod.mk_add_mk, add_zero]
  map_smul' c p := by
    apply Subtype.ext
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    change coefficients (F.relativeSquarePolynomial w hw (c • p)) α =
      coefficients (c • F.relativeSquarePolynomial w hw p) α
    rw [map_smul, Finsupp.smul_apply]
    apply Subtype.ext
    change (coefficients (F.relativeSquarePolynomial w hw (c • p)) α : L × L) =
      c • (coefficients (F.relativeSquarePolynomial w hw p) α : L × L)
    rw [F.relativeSquarePolynomial_coefficient, F.relativeSquarePolynomial_coefficient]
    change (coefficients (c • p.val.val) α, 0) = _
    simp only [map_smul, Finsupp.smul_apply, Prod.smul_mk, smul_zero]

noncomputable def relativeSquareSymbolMap :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.squareFiltration.PolynomialSymbol w :=
  (F.squareFiltration.polynomialSymbolMap w).toLinearMap.comp (F.relativeSquareLift w hw)

theorem relativeSquareSymbolMap_eq_zero_iff (p : F.normalizedRelativeSubmodule w) :
    F.relativeSquareSymbolMap w hw p = 0 ↔ p.val ∈ F.shiftedPolynomialIdeal w 2 := by
  change F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw p) = 0 ↔ _
  rw [F.squareFiltration.polynomialSymbolMap_eq_zero_iff]
  constructor
  · intro hp α
    have ha := hp α
    change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈
      F.squareLayer (Finsupp.weight w α + 1) at ha
    rw [F.relativeSquarePolynomial_coefficient] at ha
    change coefficients p.val.val α ∈ F.layer (Finsupp.weight w α + 2)
    simpa only [sub_zero] using ha.2.2
  · intro hp α
    change (coefficients (F.relativeSquarePolynomial w hw p) α : L × L) ∈
      F.squareLayer (Finsupp.weight w α + 1)
    rw [F.relativeSquarePolynomial_coefficient]
    refine ⟨p.property.1 α, (F.layer _).zero_mem, ?_⟩
    change coefficients p.val.val α - 0 ∈ F.layer (Finsupp.weight w α + 2)
    rw [sub_zero]
    exact hp α

noncomputable def normalizedRelativeFirstJet : F.normalizedRelativeSubmodule w →ₗ[ℚ] F.FilteredFirstJet w :=
  (F.filteredFirstJetMap w).toLinearMap.comp (F.normalizedRelativeSubmodule w).subtype

theorem relativeSquareSymbolMap_eq_iff (p q : F.normalizedRelativeSubmodule w) :
    F.relativeSquareSymbolMap w hw p = F.relativeSquareSymbolMap w hw q ↔
      F.normalizedRelativeFirstJet w p = F.normalizedRelativeFirstJet w q := by
  rw [← sub_eq_zero, ← map_sub, F.relativeSquareSymbolMap_eq_zero_iff]
  rw [← sub_eq_zero, ← map_sub]
  exact (F.filteredFirstJetMap_eq_zero_iff w (p - q).val).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
