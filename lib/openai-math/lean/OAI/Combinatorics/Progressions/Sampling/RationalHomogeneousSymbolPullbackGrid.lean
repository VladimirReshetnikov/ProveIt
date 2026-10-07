import OAI.Combinatorics.Progressions.Lattices.IntegerHomogeneousSymbolPullbackGrid

namespace OAI

section

namespace Erdos3
open Module MvPolynomial
open scoped TensorProduct

namespace VectorPolynomial

variable {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem CoefficientGrid.realChartSubstitute_rational
    (b : Basis ι ℝ V) (q D d : ℕ) (P : VectorPolynomial σ ℚ V)
    (hdegree : DegreeLE (fun _ => 1) d P) (hP : CoefficientGrid b q P)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, realPolynomialCoefficientGrid D (A i)) :
    CoefficientGrid b (q * D ^ d) (realChartSubstitute A P) := by
  rw [coefficientGrid_iff_coordinate]
  intro i
  rw [coordinate_realChartSubstitute_for_grid]
  exact realPolynomialCoefficientGrid_substitute
    (coordinate (b.coord i).toAddMonoidHom P) A q D d
    ((degreeLE_one_iff_basis_totalDegree b d P).mp hdegree i)
    ((coefficientGrid_iff_coordinate b q P).mp hP i) hA

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem realGradedSymbolPolynomial_degreeLE_one
    (hw : ∀ i, 0 < w i) (R : F.RealPolynomialSymbolGroup w) :
    DegreeLE (fun _ => 1) s (F.realGradedSymbolPolynomial b ω hF w R.coord) := by
  intro α hα
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  apply F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w R.coord α i
  have hi := F.adaptedBasis_weight_le_step b ω hF i
  have hweight := exponentSum_le_positive_weight w hw α
  have hone : Finsupp.weight (fun _ : σ => 1) α = α.sum (fun _ n => n) := by
    simp [Finsupp.weight_apply]
  rw [hone] at hα
  omega

theorem symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid
    (hw : ∀ i, 0 < w i)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (q D : ℕ) (hAD : ∀ i, realPolynomialCoefficientGrid D (A i))
    (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v (q * D ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_of_gradedPolynomial b ω hF v (q * D ^ s)
  change CoefficientGrid _ (q * D ^ s)
    (F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v A R.coord))
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v A hA]
  with_reducible exact (CoefficientGrid.realChartSubstitute_rational
    (V := ℝ ⊗[ℚ] F.AssociatedGraded)
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) q D s
    (F.realGradedSymbolPolynomial b ω hF w R.coord)
    (F.realGradedSymbolPolynomial_degreeLE_one b ω hF w hw R) hR A hAD)

theorem symbolRationalGrid_homogeneousPullback_rational
    (hw : ∀ i, 0 < w i)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (q D : ℕ) (hAD : ∀ i, realPolynomialCoefficientGrid D (A i))
    (R : F.RealPolynomialSymbolGroup w)
    (hR : F.SymbolRationalGrid b ω hF w q R) :
    F.SymbolRationalGrid b ω hF v (q * D ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid
    b ω hF w v hw A hA q D hAD R
  obtain ⟨z, hz⟩ := F.realGradedSymbolPolynomial_rational_coefficients b ω hF w q R hR
  exact fun α => ⟨fun i => z (α, i), funext fun i => congrFun hz (α, i)⟩

theorem symbolRationalGrid_rationalTopPullback
    (hw : ∀ i, 0 < w i) (A : σ → MvPolynomial τ ℝ)
    (q D : ℕ) (hAD : ∀ i, realPolynomialCoefficientGrid D (A i))
    (R : F.RealPolynomialSymbolGroup w)
    (hR : F.SymbolRationalGrid b ω hF w q R) :
    F.SymbolRationalGrid b ω hF v (q * D ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (A i))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) R) := by
  apply F.symbolRationalGrid_homogeneousPullback_rational b ω hF w v hw _ _ q D ?_ R hR
  intro i
  exact realPolynomialCoefficientGrid_weightedHomogeneousComponent v (w i) D _ (hAD i)

end NilpotentLieFiltration
end Erdos3

end

end OAI
