import OAI.Combinatorics.Progressions.Estimates.HomogeneousRealSymbolPullback

namespace OAI

section

namespace Erdos3
open Module MvPolynomial
open scoped TensorProduct

namespace VectorPolynomial

variable {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coordinate_realChartSubstitute_for_grid
    (A : σ → MvPolynomial τ ℝ) (f : V →ₗ[ℝ] ℝ)
    (P : VectorPolynomial σ ℚ V) :
    coordinate f.toAddMonoidHom (realChartSubstitute A P) =
      aeval A (coordinate f.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro u
  rw [← coordinate_eval₂, eval₂_realChartSubstitute, coordinate_eval₂]
  exact (MvPolynomial.comp_aeval_apply A (MvPolynomial.aeval u) _).symm

omit [IsScalarTower ℚ ℝ V] in
theorem coefficientGrid_iff_coordinate (b : Basis ι ℝ V) (q : ℕ)
    (P : VectorPolynomial σ ℚ V) :
    CoefficientGrid b q P ↔
      ∀ i, realPolynomialCoefficientGrid q (coordinate (b.coord i).toAddMonoidHom P) := by
  constructor
  · intro h i
    choose z hz using h
    refine ⟨fun α => z α i, funext fun α => ?_⟩
    simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
      Pi.smul_apply, smul_eq_mul]
      using congrFun (hz α) i
  · intro h α
    choose z hz using h
    refine ⟨fun i => z i α, funext fun i => ?_⟩
    simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
      Pi.smul_apply, smul_eq_mul]
      using congrFun (hz i) α

theorem CoefficientGrid.realChartSubstitute_integral
    (b : Basis ι ℝ V) (q : ℕ) (P : VectorPolynomial σ ℚ V)
    (hP : CoefficientGrid b q P) (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, realPolynomialCoefficientGrid 1 (A i)) :
    CoefficientGrid b q (realChartSubstitute A P) := by
  rw [coefficientGrid_iff_coordinate]
  intro i
  rw [coordinate_realChartSubstitute_for_grid]
  exact realPolynomialCoefficientGrid_aeval_integral
    (coordinate (b.coord i).toAddMonoidHom P) A q
    ((coefficientGrid_iff_coordinate b q P).mp hP i) hA

end VectorPolynomial

namespace NilpotentLieFiltration
open VectorPolynomial
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (v : τ → ℕ)

theorem symbolRationalGrid_homogeneousPullback_of_coefficientGrid
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (hAZ : ∀ i, realPolynomialCoefficientGrid 1 (A i))
    (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_of_gradedPolynomial b ω hF v q
  change CoefficientGrid _ q
    (F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v A R.coord))
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v A hA]
  with_reducible exact (CoefficientGrid.realChartSubstitute_integral
    (V := ℝ ⊗[ℚ] F.AssociatedGraded)
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
    (F.realGradedSymbolPolynomial b ω hF w R.coord) hR A hAZ)

theorem symbolRationalGrid_homogeneousPullback_integral
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, (A i).IsWeightedHomogeneous v (w i))
    (hAZ : ∀ i, realPolynomialCoefficientGrid 1 (A i))
    (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : F.SymbolRationalGrid b ω hF w q R) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v A hA R) := by
  apply F.symbolRationalGrid_homogeneousPullback_of_coefficientGrid b ω hF w v A hA hAZ q R
  obtain ⟨z, hz⟩ := F.realGradedSymbolPolynomial_rational_coefficients b ω hF w q R hR
  exact fun α => ⟨fun i => z (α, i), funext fun i => congrFun hz (α, i)⟩

theorem symbolRationalGrid_integerTopPullback
    (βZ : σ → MvPolynomial τ ℤ) (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : F.SymbolRationalGrid b ω hF w q R) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (MvPolynomial.map (Int.castRingHom ℝ) (βZ i)))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) R) := by
  apply F.symbolRationalGrid_homogeneousPullback_integral b ω hF w v _ _ ?_ q R hR
  intro i
  exact realPolynomialCoefficientGrid_weightedHomogeneousComponent v (w i) 1 _
    (realPolynomialCoefficientGrid_intCast (βZ i))

theorem symbolRationalGrid_integerTopPullback_of_coefficientGrid
    (βZ : σ → MvPolynomial τ ℤ) (q : ℕ) (R : F.RealPolynomialSymbolGroup w)
    (hR : CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
      (F.realGradedSymbolPolynomial b ω hF w R.coord)) :
    F.SymbolRationalGrid b ω hF v q
      (F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (MvPolynomial.map (Int.castRingHom ℝ) (βZ i)))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) R) := by
  apply F.symbolRationalGrid_homogeneousPullback_of_coefficientGrid b ω hF w v _ _ ?_ q R hR
  intro i
  exact realPolynomialCoefficientGrid_weightedHomogeneousComponent v (w i) 1 _
    (realPolynomialCoefficientGrid_intCast (βZ i))

end NilpotentLieFiltration
end Erdos3

end

end OAI
