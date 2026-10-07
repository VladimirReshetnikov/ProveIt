import OAI.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

namespace NilpotentLieFiltration

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
  [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
  [Fintype κ] [DecidableEq κ] (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAdjoint_matrix
    (b : Basis κ ℝ (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)))
    (D : Matrix κ (FirstCoefficientIndex w ω) ℚ)
    (S : Matrix (FirstCoefficientIndex w ω) κ ℚ)
    (hD : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ =
      D.map (Rat.castHom ℝ))
    (hDS : D * S = 1)
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap =
      D.map (Rat.castHom ℝ) *
        LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
          (F.realFirstCoefficientBasis e ω hF w) (F.realFirstCoefficientAdjoint w g).toLinearMap *
        S.map (Rat.castHom ℝ) := by
  have hsection : LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w) b
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ *
      S.map (Rat.castHom ℝ) = 1 := by
    rw [hD]
    exact real_matrix_right_inverse D S hDS
  have h := quotient_action_matrix (F.realFirstCoefficientBasis e ω hF w) b
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (F.realFirstCoefficientAdjoint w g).toLinearMap
    (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap
    (fun x => (F.realFastCoefficientAdjoint_mk w hw U g hg x).symm)
    (S.map (Rat.castHom ℝ)) hsection
  exact h.trans (congrArg (fun P : Matrix κ (FirstCoefficientIndex w ω) ℝ =>
    P * LinearMap.toMatrix (F.realFirstCoefficientBasis e ω hF w)
      (F.realFirstCoefficientBasis e ω hF w) (F.realFirstCoefficientAdjoint w g).toLinearMap *
      S.map (Rat.castHom ℝ)) hD)

end NilpotentLieFiltration
end Erdos3

end

end OAI
