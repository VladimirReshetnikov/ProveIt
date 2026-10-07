import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable def candidateSideCutoff (bound : ℝ) : ℕ := Nat.ceil bound + 1

theorem candidateSideCutoff_pos (bound : ℝ) : 0 < candidateSideCutoff bound :=
  Nat.succ_pos _

theorem lt_candidateSideCutoff (bound : ℝ) : bound < (candidateSideCutoff bound : ℝ) := by
  have hceil := Nat.le_ceil bound
  simp only [candidateSideCutoff, Nat.cast_add, Nat.cast_one]
  linarith

theorem candidateSideCutoff_lt_max_add_two (bound : ℝ) :
    (candidateSideCutoff bound : ℝ) < max bound 0 + 2 := by
  have hmono : (Nat.ceil bound : ℝ) ≤ Nat.ceil (max bound 0) := by
    exact_mod_cast Nat.ceil_mono (le_max_left bound 0)
  have hceil := Nat.ceil_lt_add_one (le_max_right bound 0)
  simp only [candidateSideCutoff, Nat.cast_add, Nat.cast_one]
  linarith

noncomputable def candidateSideCutoffCost (bound : ℝ) : ℝ :=
  Real.log ((max (candidateSideCutoff bound) 1 : ℕ) : ℝ)

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def realThresholdKeep (bound : ℝ) :
    P.productive → LayerSamplerVariables G I n B → Prop :=
  P.thresholdKeep (candidateSideCutoff bound)

namespace AxisFreezing

variable {P} {bound : ℝ}
    (freezing : P.AxisFreezing (P.realThresholdKeep bound) (candidateSideCutoffCost bound))

theorem realThreshold_long (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : (freezing.problem.chart z).keep i) :
    (candidateSideCutoff bound : ℝ) ≤ layerSamplerBox B U b S i := by
  have hs : candidateSideCutoff bound ≤ A.sides i := hi.2
  have he : layerSamplerBox B U b S i = (A.sides i : ℝ) := by
    cases i <;> rfl
  rw [he]
  exact_mod_cast hs

theorem realThreshold_strict_long (z : P.productive) (i : LayerSamplerVariables G I n B)
    (hi : (freezing.problem.chart z).keep i) :
    bound < layerSamplerBox B U b S i :=
  (lt_candidateSideCutoff bound).trans_le (freezing.realThreshold_long z i hi)

end AxisFreezing

theorem exists_realThresholdAxisFreezing (bound : ℝ) :
    ∃ freezing : P.AxisFreezing (P.realThresholdKeep bound) (candidateSideCutoffCost bound),
      (∀ z : P.productive, ∀ i, (freezing.problem.chart z).keep i →
        (candidateSideCutoff bound : ℝ) ≤ layerSamplerBox B U b S i) ∧
      (∀ z : P.productive, ∀ i, (freezing.problem.chart z).keep i →
        bound < layerSamplerBox B U b S i) := by
  obtain ⟨freezing⟩ := P.exists_thresholdAxisFreezing (candidateSideCutoff bound)
  exact ⟨freezing, freezing.realThreshold_long, freezing.realThreshold_strict_long⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
