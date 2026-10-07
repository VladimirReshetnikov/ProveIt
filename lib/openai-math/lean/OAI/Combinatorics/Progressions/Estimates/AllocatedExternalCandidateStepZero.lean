import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d : ℕ}
    (D : RationalFilteredNilmanifold L 0 d) (Fmark : NilpotentLieFiltration M 0)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AllocatedExternalCandidateProblem

theorem ambientScore_one_eq (z : P.productive) :
    P.ambientScore 1 z (P.chart z).slice.integerPoints =
      (P.candidate z).score observable weight := by
  unfold ambientScore AllocatedExternalLocalCandidate.score AllocatedExternalLocalCandidate.value
  congr 2
  funext u
  congr 2
  apply congrArg QuotientGroup.mk
  exact (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).trans
    (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).symm

theorem conclusion_stepZero : Nonempty (P.Conclusion cost massThreshold scoreThreshold) := by
  classical
  refine ⟨{
    ambient := 1
    marked := ?_
    retained := P.productive
    subset := fun _ h => h
    mass := P.mass
    step := fun z => (P.chart z).step
    step_pos := fun z => (P.chart z).step_pos
    slice := fun z => (P.chart z).slice
    dense := fun z => (P.chart z).dense
    inside := fun _ _ h => h
    score := ?_
  }⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    exact (Fmark.realification.externalCandidate_stepZero_coord_eq_zero _).trans
      (Fmark.realification.externalCandidate_stepZero_coord_eq_zero _).symm
  · intro z
    rw [P.ambientScore_one_eq]
    exact P.score z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
