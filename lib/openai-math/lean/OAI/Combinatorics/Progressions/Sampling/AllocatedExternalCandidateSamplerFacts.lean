import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartKeepBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem chart_recovered_at_common_center (z : P.productive) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      P.centerLift z.val.1.val z.val.2.val (P.chart z).sample (P.chart z).read := by
  have h := (P.chart z).recovered
  rw [P.chart_centerLift z, P.chart_path z] at h
  exact h

theorem currentGrade_spatial_support (z : P.productive) :
    z.val.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
  simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
    using z.val.2.property

theorem currentGrade_sampler_facts (z : P.productive) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      P.centerLift z.val.1.val z.val.2.val (P.chart z).sample (P.chart z).read ∧
    z.val.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 ∧
    (∀ i : {i // ¬(P.chart z).keep i},
      0 ≤ (P.chart z).fixed i ∧ (P.chart z).fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val) := by
  exact ⟨P.chart_recovered_at_common_center z, P.currentGrade_spatial_support z,
    (P.chart z).fixed_in_box⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
