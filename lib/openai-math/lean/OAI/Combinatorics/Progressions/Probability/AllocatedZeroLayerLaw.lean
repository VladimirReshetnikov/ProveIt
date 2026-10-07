import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

omit [Fintype X] in

@[simp] theorem allocatedCenteredJointDensity_zero_layers
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z = 1 := by
  simp only [allocatedCenteredJointDensity, allocatedCoefficientDensity,
    canonicalCoefficientDensity, Finset.univ_eq_empty, Finset.prod_empty]

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

theorem allocatedCenteredJointDensityMass_zero_layers
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hwidth : ∀ z, 0 < allocatedExternalCandidateWidths B U b S N τ ξ z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z) :
    selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N)) stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ)
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center) = 1 := by
  rw [← selectedJointReference_densityMass _ hbase _ _ _ hwidth hZ]
  simp only [allocatedCenteredJointDensity_zero_layers, FiniteProbabilityWeights.mean_const]

theorem allocatedExternalCandidateSampler_zero_layers
    (hN : ∀ x, 0 < N x) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hstride : ∀ x, 0 < stride x)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z) :
    AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center := by
  refine ⟨hN, hτ, hξ, hstride, hbase, hZ, ?_⟩
  rw [allocatedCenteredJointDensityMass_zero_layers B U b S hb o hR hσ poly hm
    center N τ ξ stride cells hbase
    (narrowTrimmedSpatialWidths_pos (allocatedExternalCandidateRootBudget_nonneg B U b S)
      hτ hξ N hN) hZ]
  norm_num

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem AllocatedExternalCandidateSampler.law_zero_layers
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ stride cells center) :
    A.law = selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
      A.bases_nonempty stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
      A.widths_pos A.smooth_mass_pos := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  rw [AllocatedExternalCandidateSampler.law, selectedJointFiniteLaw,
    FiniteProbabilityWeights.reweightPositive_weight]
  simp only [allocatedCenteredJointDensity_zero_layers, FiniteProbabilityWeights.mean_const,
    mul_one, div_one]

end Erdos3.VectorPolynomial

end

end OAI
