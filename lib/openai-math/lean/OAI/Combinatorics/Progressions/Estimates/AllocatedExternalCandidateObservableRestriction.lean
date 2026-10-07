import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw
import OAI.Combinatorics.Progressions.Sampling.MarkedExternalKernelProjectionScoreRestoration

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

noncomputable def restrictObservable
    (newObservable : (X → ℤ) → D.Space → ℂ)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained,
      newScore ≤ (P.candidate ⟨z.val,hsub z.property⟩).score newObservable weight) :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked newObservable weight
      cost newMass newScore where
  productive := retained
  mass := hmass
  chart z := P.chart ⟨z.val,hsub z.property⟩
  chart_path z := P.chart_path ⟨z.val,hsub z.property⟩
  centerLift := P.centerLift
  chart_centerLift z := P.chart_centerLift ⟨z.val,hsub z.property⟩
  frozen_side z := P.frozen_side ⟨z.val,hsub z.property⟩
  candidate z := P.candidate ⟨z.val,hsub z.property⟩
  score := hscore

@[simp] theorem restrictObservable_physicalIntegerPoint
    (newObservable : (X → ℤ) → D.Space → ℂ)
    (retained : Finset A.Path) (hsub : retained ⊆ P.productive)
    {newMass newScore : ℝ} (hmass : newMass ≤ A.law.mass retained)
    (hscore : ∀ z : retained,
      newScore ≤ (P.candidate ⟨z.val,hsub z.property⟩).score newObservable weight) :
    (P.restrictObservable newObservable retained hsub hmass hscore).physicalIntegerPoint =
      P.physicalIntegerPoint := rfl

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
