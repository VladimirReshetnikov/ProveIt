import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerDetectorReturn

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    (τ ξ : ℝ) (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedExternalCandidateSampler_of_scalarReference_empty_layers
    (hN : ∀ x, 0 < N x) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := G) ((Fintype.card G : ℝ) * S.value) τ N) z) :
    AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ (fun _ : X => 1) {0} center := by
  apply allocatedExternalCandidateSampler_empty_layers B U b S hb o hR hσ poly hm
    center N τ ξ (fun _ : X => 1) {0} hN hτ hξ (fun _ => by norm_num) hbase
  rw [allocatedExternalCandidateWidths_empty_layers]
  rw [← selectedResidueSmoothMass_scalarCoordinateEquiv (emptyLayerVariablesEquiv B)
    ((Fintype.card G : ℝ) * S.value) τ N]
  exact hZ

end Erdos3.VectorPolynomial

end

end OAI
