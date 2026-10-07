import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrimitiveFrontDescentData

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem allocatedCandidate_initialLong_excluded_bound
    {K : Type*} (side : K → ℝ) (oldKeep : K → Prop)
    {cost initialShortLog : ℝ}
    (hshort : ∀ i, ¬oldKeep i → side i ≤ Real.exp cost) :
    ∀ i, ¬(oldKeep i ∧ Real.exp initialShortLog ≤ side i) →
      side i ≤ Real.exp (max cost initialShortLog) := by
  intro i hi
  by_cases hold : oldKeep i
  · have hside : ¬Real.exp initialShortLog ≤ side i := fun hs => hi ⟨hold, hs⟩
    exact (lt_of_not_ge hside).le.trans
      (Real.exp_le_exp.mpr (le_max_right cost initialShortLog))
  · exact (hshort i hold).trans
      (Real.exp_le_exp.mpr (le_max_left cost initialShortLog))

theorem allocatedCandidate_retainedMass_pos {massLog retainedLoss massH : ℝ}
    (hmass : Real.exp (-massLog) ≤ massH) :
    0 < Real.exp (-retainedLoss) * massH :=
  mul_pos (Real.exp_pos _) ((Real.exp_pos _).trans_le hmass)

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler.InnerSourceProfile

variable {degree : ℕ} (source : A.InnerSourceProfile degree)

noncomputable abbrev stageKeep (r : ℕ) (i : LayerSamplerVariables G I n B) : Prop :=
  Real.exp (allocatedCandidateStageSlice degree m source.Cprimitive
    (preparedFiniteForwardParameter source.scheduleExponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants r source.x)) ≤
    (A.sides i : ℝ)

theorem stageKeep_kept :
    ∀ r i, source.stageKeep r i →
      Real.exp (allocatedCandidateStageSlice degree m source.Cprimitive
        (preparedFiniteForwardParameter source.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants r source.x)) ≤
        (A.sides i : ℝ) :=
  fun _ _ h => h

theorem stageKeep_frozen :
    ∀ r i, ¬source.stageKeep r i →
      (A.sides i : ℝ) ≤
        Real.exp (allocatedCandidateStageSlice degree m source.Cprimitive
          (preparedFiniteForwardParameter source.scheduleExponent
            AllocatedExternalCandidateSampler.degreeSourceCountConstants r source.x)) := by
  intro r i hi
  exact (lt_of_not_ge hi).le

theorem stageKeep_subset_initialLong
    (initialLong : LayerSamplerVariables G I n B → Prop) {initialShortCost : ℝ}
    (hshortCost : initialShortCost ≤ (source.x + source.Cprimitive) ^ source.Cprimitive)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp initialShortCost) :
    ∀ r i, source.stageKeep r i → initialLong i := by
  intro r
  exact allocatedCandidateStage_keep_subset_initialLong
    (fun i => (A.sides i : ℝ)) initialLong (source.stageKeep r)
    degree m source.Cprimitive source.scheduleExponent r source.x_nonneg
    hshortCost hshort (source.stageKeep_kept r)

theorem detectionLoss_le_retainedMass {massLog retainedLoss massH : ℝ}
    (hmass : Real.exp (-massLog) ≤ massH)
    (hbudget : retainedLoss + massLog ≤ source.gainLog) :
    ∀ r < degree, source.detectionLoss r ≤
      (9 / 10 : ℝ) * (Real.exp (-retainedLoss) * massH) := by
  have hexp : Real.exp (-source.gainLog) ≤ Real.exp (-retainedLoss) * massH := by
    calc
      _ ≤ Real.exp (-(retainedLoss + massLog)) :=
        Real.exp_le_exp.mpr (neg_le_neg hbudget)
      _ = Real.exp (-retainedLoss) * Real.exp (-massLog) := by
        rw [neg_add, Real.exp_add]
      _ ≤ Real.exp (-retainedLoss) * massH :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)
  have hpos := allocatedCandidate_retainedMass_pos (retainedLoss := retainedLoss) hmass
  intro r hr
  have hloss := source.loss_bound r hr
  linarith only [hloss, hexp, hpos]

theorem detectionLoss_le_spatialNativeMass
    {Pivot : Type*} [Fintype Pivot] {qVertical qCommon massLog massH : ℝ}
    (hmass : Real.exp (-massLog) ≤ massH)
    (hbudget : verticalDecompositionBudget qVertical * (Fintype.card Pivot : ℝ) +
      ((qCommon + 2) ^ 5 + qCommon) + massLog ≤ source.gainLog) :
    ∀ r < degree, source.detectionLoss r ≤
      (9 / 10 : ℝ) * (Real.exp (-(verticalDecompositionBudget qVertical *
        (Fintype.card Pivot : ℝ) + ((qCommon + 2) ^ 5 + qCommon))) * massH) :=
  source.detectionLoss_le_retainedMass hmass hbudget

theorem markHeight_bounds {markBudget : ℝ} (hmark : 0 ≤ markBudget)
    (hmarkInput : markBudget + 1 ≤ source.x) :
    1 ≤ ⌈Real.exp markBudget⌉₊ ∧
      (⌈Real.exp markBudget⌉₊ : ℝ) ≤ Real.exp source.x :=
  ⟨one_le_ceil_exp _,
    (ceil_exp_le_exp_add_one hmark).trans (Real.exp_le_exp.mpr hmarkInput)⟩

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

theorem retained_nonempty : data.retained.Nonempty := by
  by_contra h
  have hzero : A.law.mass data.retained = 0 := by
    rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp [FiniteProbabilityWeights.mass]
  linarith only [data.mass_pos, hzero]

theorem initialLong_nonempty [Nonempty G] {initialShort : ℝ}
    (hcost : cost < source.inner.x) (hshort : initialShort ≤ source.inner.x)
    (hscale : Real.exp source.inner.x ≤ (S.value : ℝ)) :
    Nonempty {i : LayerSamplerVariables G I n B //
      data.front.keep i ∧ Real.exp initialShort ≤ (A.sides i : ℝ)} := by
  obtain ⟨a, _⟩ := data.retained_nonempty
  let i : LayerSamplerVariables G I n B := .inl (Classical.choice inferInstance)
  have hside : Real.exp source.inner.x ≤ (A.sides i : ℝ) := hscale
  have hkeep : data.front.keep i := by
    by_contra hi
    exact (not_lt_of_ge (data.frozen_side a ⟨i, hi⟩))
      ((Real.exp_lt_exp.mpr hcost).trans_le hside)
  exact ⟨⟨i, hkeep, (Real.exp_le_exp.mpr hshort).trans hside⟩⟩

theorem initialLong_excluded_bound (initialShort : ℝ) :
    ∀ i, ¬(data.front.keep i ∧ Real.exp initialShort ≤ (A.sides i : ℝ)) →
      (A.sides i : ℝ) ≤ Real.exp (max cost initialShort) := by
  obtain ⟨a, _⟩ := data.retained_nonempty
  exact allocatedCandidate_initialLong_excluded_bound (fun i => (A.sides i : ℝ))
    data.front.keep (fun i hi => data.frozen_side a ⟨i, hi⟩)

theorem initialLong_excluded_bound_of_cost_le {initialShort : ℝ}
    (hcost : cost ≤ initialShort) :
    ∀ i, ¬(data.front.keep i ∧ Real.exp initialShort ≤ (A.sides i : ℝ)) →
      (A.sides i : ℝ) ≤ Real.exp initialShort := by
  simpa only [max_eq_right hcost] using data.initialLong_excluded_bound initialShort

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
