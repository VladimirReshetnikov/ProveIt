/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def realHorizontalSymbolHom (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.RealPolynomialSymbolGroup w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) where
  toFun X := Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord)
  map_one' := by
    change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ 0) = 1
    rw [map_zero]
    rfl
  map_mul' X Y := by
    change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (lieBCH s X.coord Y.coord)) = Multiplicative.ofAdd
        ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord +
          (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ Y.coord)
    exact congrArg Multiplicative.ofAdd (linearMap_baseChange_lieBCH_eq_add
      (F.higherHorizontalSymbolCoefficient w α) (F.higherHorizontalSymbolCoefficient_lie w α)
      hs X.coord Y.coord)

@[simp] theorem realHorizontalSymbolHom_apply (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (X : F.associatedDegree.RealPolynomialSymbolGroup w) :
    Multiplicative.toAdd (F.realHorizontalSymbolHom hs w α X) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord := rfl

theorem realHorizontalSymbolCoefficient_extended (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (F.associatedDegree.realExtendedSymbolMap w x) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    change (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (a ⊗ₜ[ℚ] F.associatedDegree.polynomialSymbolMap w p) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ (a ⊗ₜ[ℚ] p)
    simp only [LinearMap.baseChange_tmul, F.higherHorizontalSymbolCoefficient_map]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realHorizontalPolynomialHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    (F.associatedDegree.realification.adaptedPolynomialFiltration w).Group →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalSymbolHom hs w α).comp
    (F.associatedDegree.realPolynomialSymbolHom b ω hF w)

theorem realHorizontalPolynomialHom_tensor (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    Multiplicative.toAdd (F.realHorizontalPolynomialHom hs b ω hF w α
      ⟨F.associatedDegree.realAdaptedPolynomialTensor w x⟩) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  change (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    (F.associatedDegree.realSymbolOfPolynomial b ω hF w
      (F.associatedDegree.realAdaptedPolynomialMap w x)) = _
  rw [F.associatedDegree.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact F.realHorizontalSymbolCoefficient_extended w α x

end Erdos3.DegreeRankLieFiltration

end

end OAI
