import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateNativeFrozenScore

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

theorem refilteredLocalCoordinates_eq_of_log
    (nativeMiddle : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hlog : ∀ z, map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (middle z).orbit.log = ((nativeMiddle z).coord :
          VectorPolynomial (P.chart z).Variables ℚ (ℝ ⊗[ℚ] L)))
    (z : P.productive) :
    P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z =
      nativeMiddle z := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact hlog z

theorem refilteredLocalCoordinates_factor_of_log
    (left nativeMiddle right : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hlog : ∀ z, map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (middle z).orbit.log = ((nativeMiddle z).coord :
          VectorPolynomial (P.chart z).Variables ℚ (ℝ ⊗[ℚ] L)))
    (hfactor : ∀ z, left z * nativeMiddle z * right z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (z : P.productive) :
    left z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
      markedMiddle middle z * right z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit := by
  rw [P.refilteredLocalCoordinates_eq_of_log A Fmark φ hφ W Dref hDref Fref
    markedMiddle middle nativeMiddle hlog z]
  exact hfactor z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
