import OAI.Combinatorics.Progressions.Estimates.RealNormalizedSquareFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem adaptedReducedRealSymbolHom_square_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.squareFiltration.adaptedReducedRealSymbolHom w (F.realSquareDiagonalPolynomialHom w g) =
      F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) := by
  have hcomp : (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap =
        (F.reducedSquareDiagonalSymbolMap w).toLinearMap.comp (F.adaptedReducedSymbolMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    change F.reducedSquareSymbolMap w
        (F.squareFiltration.polynomialSymbolMap w (F.squareDiagonalPolynomialMap w p)) =
      F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolMap w (F.polynomialSymbolMap w p))
    rw [← F.squareDiagonalSymbolMap_symbol, F.reducedSquareDiagonalSymbolMap_quotient]
  apply NilpotentLieBCHGroup.ext
  change (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ
        ((F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

theorem adaptedReducedRealSymbolHom_square_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.squareFiltration.adaptedReducedRealSymbolHom w (F.realRelativeSquarePolynomial w hw x) =
      (⟨F.realReducedRelativeSquareSymbolMap w hw x⟩ :
        F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) := by
  have hcomp : (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.comp
      (F.relativeSquareLift w hw) = F.reducedRelativeSquareSymbolMap w hw := by
    apply LinearMap.ext
    intro p
    rfl
  apply NilpotentLieBCHGroup.ext
  change (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

theorem adaptedReducedRealSymbolHom_square_projection
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.reducedSquareRealSymbolHom w (F.squareFiltration.adaptedReducedRealSymbolHom w r) =
      F.adaptedReducedRealSymbolHom w (F.realSquareSndPolynomialHom w r) := by
  have hcomp : (F.reducedSquareSndSymbolMap w).toLinearMap.comp
      (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap =
        (F.adaptedReducedSymbolMap w).toLinearMap.comp (F.squareSndPolynomialMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    change F.reducedSquareSndSymbolMap w
        (F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w p)) =
      F.quotientTopSymbolMap w (F.polynomialSymbolMap w (F.squareSndPolynomialMap w p))
    rw [F.reducedSquareSndSymbolMap_quotient, F.squareSndSymbolMap_symbol]
  apply NilpotentLieBCHGroup.ext
  change (F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ
    ((F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ r.coord) =
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
        ((F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ r.coord)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

theorem realReducedRelativeSquareSymbolMap_of_square_factorization (hw : ∀ i, 0 < w i)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hr : r = F.realRelativeSquarePolynomial w hw x * F.realSquareDiagonalPolynomialHom w g) :
    F.realReducedRelativeSquareSymbolMap w hw x =
      (F.reducedSquareRealRelativePart w (F.squareFiltration.adaptedReducedRealSymbolHom w r)).coord := by
  rw [hr, map_mul, F.adaptedReducedRealSymbolHom_square_relative,
    F.adaptedReducedRealSymbolHom_square_diagonal]
  let k : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
    ⟨F.realReducedRelativeSquareSymbolMap w hw x⟩
  have hk : F.reducedSquareRealSymbolHom w k = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact F.realReducedRelativeSquareSymbolMap_projection w hw x
  have he := F.reducedSquareRealRelativePart_of_factors w k (F.adaptedReducedRealSymbolHom w g) hk
  exact (congrArg NilpotentLieBCHGroup.coord he).symm

variable [Fintype σ] (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem normalized_real_square_derivative_identity (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-e) (-m) (F.realAdaptedPolynomialMap (fun _ => 1) g.coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) g.coord) :
    F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) =
      F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) := by
  obtain ⟨x, hx, hr, _⟩ := F.exists_real_normalized_square_factors b ω hF h e m g r hf hs
  exact F.real_normalized_square_coefficient_identity b ω hF h e m g _ x
    (F.realReducedRelativeSquareSymbolMap_of_square_factorization (fun _ => 1)
      (fun _ => Nat.zero_lt_one) r g x hr) hx

end Erdos3.NilpotentLieFiltration

end

end OAI
