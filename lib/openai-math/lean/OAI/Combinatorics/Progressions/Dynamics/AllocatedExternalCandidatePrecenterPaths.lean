import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateObservableRestriction
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeReindex

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

theorem AllocatedExternalLocalCandidate.score_of_heq
    {cost : ℝ} {C C' : AllocatedExternalLocalChart (E := E) A cost}
    {candidate : AllocatedExternalLocalCandidate C D Fmark φ marked}
    {candidate' : AllocatedExternalLocalCandidate C' D Fmark φ marked}
    (hC : C = C') (hc : HEq candidate candidate')
    (obs : (X → ℤ) → D.Space → ℂ) (wgt : (X → ℤ) → ℂ) :
    candidate.score obs wgt = candidate'.score obs wgt := by
  subst C'
  cases hc
  rfl

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def precenterChart (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : AllocatedExternalLocalChart (E := E) A cost :=
  P.chart (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)

noncomputable def precenterCandidate (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : AllocatedExternalLocalCandidate (P.precenterChart hpos a) D Fmark φ marked :=
  P.candidate (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)

@[simp] theorem precenterChart_mem (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive) : P.precenterChart hpos a = P.chart ⟨a, ha⟩ := by
  unfold precenterChart
  rw [AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem]

@[simp] theorem precenterCandidate_mem (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive) :
    HEq (P.precenterCandidate hpos a) (P.candidate ⟨a, ha⟩) := by
  change HEq (P.candidate (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)) (P.candidate ⟨a, ha⟩)
  rw [AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem]

@[simp] theorem precenterChart_path (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive) : (P.precenterChart hpos a).path = a := by
  rw [P.precenterChart_mem hpos a ha]
  exact P.chart_path _

@[simp] theorem precenterChart_center (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : (P.precenterChart hpos a).centerLift = P.centerLift :=
  P.chart_centerLift _

@[simp] theorem precenterChart_keep (hpos : 0 < A.law.mass P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep) (a : A.Path) :
    (P.precenterChart hpos a).keep = keep := hkeep _

theorem precenterChart_frozen (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (i : {i // ¬(P.precenterChart hpos a).keep i}) :
    (A.sides i.val : ℝ) ≤ Real.exp cost := P.frozen_side _ i

theorem precenterCandidate_score (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : scoreThreshold ≤ (P.precenterCandidate hpos a).score observable weight :=
  P.score _

theorem precenterCandidate_score_mem_eq (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (ha : a ∈ P.productive)
    (newObservable : (X → ℤ) → D.Space → ℂ) :
    (P.precenterCandidate hpos a).score newObservable weight =
      (P.candidate ⟨a, ha⟩).score newObservable weight := by
  change (P.candidate (AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract
    A.law P.productive hpos a)).score newObservable weight = _
  rw [AllocatedExternalCandidateSpatialNativeFamily.positiveMassRetract_mem]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
