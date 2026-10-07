import OAI.Combinatorics.Progressions.Linear.SquareSymbolProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

def squareDiagonalLie : L →ₗ⁅ℚ⁆ F.squareLieSubalgebra where
  toFun x := ⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  map_lie' := Subtype.ext rfl

noncomputable def squareFstPolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F F.squareFst (fun _ _ hx => hx.1) w

noncomputable def squareSndPolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F F.squareSnd (fun _ _ hx => hx.2.1) w

noncomputable def squareDiagonalPolynomialMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.squareFiltration.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.squareFiltration F.squareDiagonalLie
    (fun j x hx => ⟨hx, hx, by change x - x ∈ F.layer (j + 1); simp⟩) w

theorem squareFstPolynomialMap_coefficient (r : F.squareFiltration.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) : coefficients (F.squareFstPolynomialMap w r).val α =
      (coefficients r.val α).val.1 := by
  change coefficients (VectorPolynomial.map F.squareFst.toLinearMap r.val) α = _
  rw [coefficients_map]
  rfl

theorem squareSndPolynomialMap_coefficient (r : F.squareFiltration.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) : coefficients (F.squareSndPolynomialMap w r).val α =
      (coefficients r.val α).val.2 := by
  change coefficients (VectorPolynomial.map F.squareSnd.toLinearMap r.val) α = _
  rw [coefficients_map]
  rfl

theorem squareDiagonalPolynomialMap_coefficient (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    (coefficients (F.squareDiagonalPolynomialMap w p).val α).val =
      (coefficients p.val α, coefficients p.val α) := by
  change (coefficients (VectorPolynomial.map F.squareDiagonalLie.toLinearMap p.val) α).val = _
  rw [coefficients_map]
  rfl

theorem square_polynomial_ext {r q : F.squareFiltration.adaptedLieSubalgebra w}
    (hf : F.squareFstPolynomialMap w r = F.squareFstPolynomialMap w q)
    (hs : F.squareSndPolynomialMap w r = F.squareSndPolynomialMap w q) : r = q := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply Subtype.ext
  apply Prod.ext
  · have he := congrArg (fun p : F.adaptedLieSubalgebra w => coefficients p.val α) hf
    simpa only [F.squareFstPolynomialMap_coefficient] using he
  · have he := congrArg (fun p : F.adaptedLieSubalgebra w => coefficients p.val α) hs
    simpa only [F.squareSndPolynomialMap_coefficient] using he

@[simp] theorem squareFstPolynomialMap_diagonal (p : F.adaptedLieSubalgebra w) :
    F.squareFstPolynomialMap w (F.squareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareFstPolynomialMap_coefficient, F.squareDiagonalPolynomialMap_coefficient]

@[simp] theorem squareSndPolynomialMap_diagonal (p : F.adaptedLieSubalgebra w) :
    F.squareSndPolynomialMap w (F.squareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareSndPolynomialMap_coefficient, F.squareDiagonalPolynomialMap_coefficient]

@[simp] theorem squareFstPolynomialMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.squareFstPolynomialMap w (F.relativeSquareLift w hw p) = p.val := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareFstPolynomialMap_coefficient]
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.1 = _
  rw [F.relativeSquarePolynomial_coefficient]

@[simp] theorem squareSndPolynomialMap_relative (hw : ∀ i, 0 < w i)
    (p : F.normalizedRelativeSubmodule w) :
    F.squareSndPolynomialMap w (F.relativeSquareLift w hw p) = 0 := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.squareSndPolynomialMap_coefficient]
  change (coefficients (F.relativeSquarePolynomial w hw p) α).val.2 = coefficients 0 α
  rw [F.relativeSquarePolynomial_coefficient, map_zero, Finsupp.zero_apply]

noncomputable def squareDiagonalSymbolMap :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.squareFiltration F.squareDiagonalLie
    (fun j x hx => ⟨hx, hx, by change x - x ∈ F.layer (j + 1); simp⟩) w

@[simp] theorem squareDiagonalSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.squareDiagonalSymbolMap w (F.polynomialSymbolMap w p) =
      F.squareFiltration.polynomialSymbolMap w (F.squareDiagonalPolynomialMap w p) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
