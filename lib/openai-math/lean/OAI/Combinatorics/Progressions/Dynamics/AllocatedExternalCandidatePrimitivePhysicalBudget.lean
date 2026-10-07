import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateGeneratedFreezingSuccessor

namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration RationalFilteredNilmanifold

noncomputable def candidateGeneratedPhysicalGeometryParameter (s A : ℕ) (p : ℝ) : ℝ :=
  candidateCoveredGeometryParameter A (frozenMarkedPhysicalExponent (s + 1))
    (allocatedRightDictionaryExponent (s + 1)) p

structure GeneratedPhysicalSuccessorScalarBounds (s A C : ℕ) (p pOuter : ℝ) : Prop where
  input_budget : (p + A) ^ A ≤ (p + C) ^ C
  geometry_one : 1 ≤ candidateGeneratedPhysicalGeometryParameter s A p
  input_geometry : p ≤ candidateGeneratedPhysicalGeometryParameter s A p
  outer_geometry : pOuter ≤ candidateGeneratedPhysicalGeometryParameter s A p
  outer_budget : pOuter ≤ (p + C) ^ C
  physical_geometry :
    (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) ≤
      candidateGeneratedPhysicalGeometryParameter s A p
  right_geometry :
    ((pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) +
      allocatedRightDictionaryExponent (s + 1)) ^ allocatedRightDictionaryExponent (s + 1) ≤
      candidateGeneratedPhysicalGeometryParameter s A p
  geometry_budget : candidateGeneratedPhysicalGeometryParameter s A p ≤ (p + C) ^ C
  covered_budget :
    (candidateGeneratedPhysicalGeometryParameter s A p + allocatedCoveredLowerExponent s 1) ^
      allocatedCoveredLowerExponent s 1 ≤ (p + C) ^ C
  geometry_recursive :
    candidateGeneratedPhysicalGeometryParameter s A p ≤ finiteFreezingRecursiveParameter C p
  covered_recursive :
    (candidateGeneratedPhysicalGeometryParameter s A p + allocatedCoveredLowerExponent s 1) ^
      allocatedCoveredLowerExponent s 1 ≤ finiteFreezingRecursiveParameter C p

theorem exists_generatedPhysicalSuccessorScalarBounds (s A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ pOuter : ℝ,
      0 ≤ pOuter → pOuter ≤ (p + A) ^ A →
      GeneratedPhysicalSuccessorScalarBounds s A C p pOuter := by
  obtain ⟨C, hC, hbound⟩ := exists_candidateCoveredParameters_bound A
    (frozenMarkedPhysicalExponent (s + 1)) (allocatedRightDictionaryExponent (s + 1))
    (allocatedCoveredLowerExponent s 1)
  refine ⟨C, hC, ?_⟩
  intro p hp pOuter hpOuter hpOuterBound
  obtain ⟨houterBudget, hgeoBudget, hcoverBudget, hpGeo, hRightGeo, hDictGeo,
    hGeoRec, hCoverRec⟩ := hbound p hp
  have hgeometry := candidateCoveredGeometryParameter_bounds A
    (frozenMarkedPhysicalExponent (s + 1)) (allocatedRightDictionaryExponent (s + 1)) hp
  have hphysical :
      (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) ≤
        candidateCoveredRightParameter A (frozenMarkedPhysicalExponent (s + 1)) p := by
    unfold candidateCoveredRightParameter candidateCoveredOuterParameter
    exact pow_le_pow_left₀
      (by positivity : 0 ≤ pOuter + (frozenMarkedPhysicalExponent (s + 1) : ℝ))
      (by linarith)
      (frozenMarkedPhysicalExponent (s + 1))
  have hright :
      ((pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) +
        allocatedRightDictionaryExponent (s + 1)) ^ allocatedRightDictionaryExponent (s + 1) ≤
        candidateCoveredDictionaryParameter A (frozenMarkedPhysicalExponent (s + 1))
          (allocatedRightDictionaryExponent (s + 1)) p := by
    unfold candidateCoveredDictionaryParameter
    exact pow_le_pow_left₀
      (by positivity : 0 ≤
        (pOuter + frozenMarkedPhysicalExponent (s + 1)) ^ frozenMarkedPhysicalExponent (s + 1) +
          (allocatedRightDictionaryExponent (s + 1) : ℝ))
      (by linarith)
      (allocatedRightDictionaryExponent (s + 1))
  exact {
    input_budget := houterBudget
    geometry_one := hgeometry.1
    input_geometry := hpGeo
    outer_geometry := hpOuterBound.trans hgeometry.2.2.1
    outer_budget := hpOuterBound.trans houterBudget
    physical_geometry := hphysical.trans hRightGeo
    right_geometry := hright.trans hDictGeo
    geometry_budget := hgeoBudget
    covered_budget := hcoverBudget
    geometry_recursive := hGeoRec
    covered_recursive := hCoverRec }

noncomputable def candidateGeneratedPhysicalBudgetExponent (s A : ℕ) : ℕ :=
  Classical.choose (exists_generatedPhysicalSuccessorScalarBounds s A)

theorem candidateGeneratedPhysicalBudgetExponent_ge_two (s A : ℕ) :
    2 ≤ candidateGeneratedPhysicalBudgetExponent s A :=
  (Classical.choose_spec (exists_generatedPhysicalSuccessorScalarBounds s A)).1

theorem candidateGeneratedPhysicalScalarBounds (s A : ℕ) {p pOuter : ℝ}
    (hp : 0 ≤ p) (hpOuter : 0 ≤ pOuter) (hpOuterBound : pOuter ≤ (p + A) ^ A) :
    GeneratedPhysicalSuccessorScalarBounds s A
      (candidateGeneratedPhysicalBudgetExponent s A) p pOuter :=
  (Classical.choose_spec (exists_generatedPhysicalSuccessorScalarBounds s A)).2
    p hp pOuter hpOuter hpOuterBound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_nativeMarkedFreezingPhysicalParameter_bound (Cfree : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ p : ℝ, 0 ≤ p →
      nativeMarkedFreezingPhysicalParameter p Cfree ≤ (p + A) ^ A := by
  let poly : Polynomial ℕ :=
    (Polynomial.X + 3) ^ 36 + (Polynomial.X + Polynomial.C Cfree) ^ Cfree
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro p hp
  simpa [poly, nativeMarkedFreezingPhysicalParameter, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

noncomputable def candidateFreezingOuterExponent (s a : ℕ) : ℕ :=
  Classical.choose (exists_nativeMarkedFreezingPhysicalParameter_bound
    (nativeMarkedFreezingExponent (s + 1) a))

theorem candidateFreezingOuterExponent_ge_two (s a : ℕ) :
    2 ≤ candidateFreezingOuterExponent s a :=
  (Classical.choose_spec (exists_nativeMarkedFreezingPhysicalParameter_bound
    (nativeMarkedFreezingExponent (s + 1) a))).1

noncomputable def candidatePrimitivePhysicalOuterParameter (s a : ℕ) (p : ℝ) : ℝ :=
  nativeMarkedFreezingPhysicalParameter p (nativeMarkedFreezingExponent (s + 1) a)

theorem candidatePrimitivePhysicalOuterParameter_bound (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitivePhysicalOuterParameter s a p ≤
      (p + candidateFreezingOuterExponent s a) ^ candidateFreezingOuterExponent s a :=
  (Classical.choose_spec (exists_nativeMarkedFreezingPhysicalParameter_bound
    (nativeMarkedFreezingExponent (s + 1) a))).2 p hp

theorem candidatePrimitivePhysicalOuterParameter_nonneg (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ candidatePrimitivePhysicalOuterParameter s a p :=
  hp.trans (nativeMarkedFreezingPhysicalParameter_bounds hp
    (nativeMarkedFreezingExponent (s + 1) a)).1

noncomputable def candidatePrimitivePhysicalBudgetExponent (s a : ℕ) : ℕ :=
  candidateGeneratedPhysicalBudgetExponent s (candidateFreezingOuterExponent s a)

theorem candidatePrimitivePhysicalBudgetExponent_ge_two (s a : ℕ) :
    2 ≤ candidatePrimitivePhysicalBudgetExponent s a :=
  candidateGeneratedPhysicalBudgetExponent_ge_two s (candidateFreezingOuterExponent s a)

noncomputable def candidatePrimitivePhysicalGeometryParameter (s a : ℕ) (p : ℝ) : ℝ :=
  candidateGeneratedPhysicalGeometryParameter s (candidateFreezingOuterExponent s a) p

theorem candidatePrimitivePhysicalScalarBounds (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    GeneratedPhysicalSuccessorScalarBounds s (candidateFreezingOuterExponent s a)
      (candidatePrimitivePhysicalBudgetExponent s a) p
      (candidatePrimitivePhysicalOuterParameter s a p) :=
  candidateGeneratedPhysicalScalarBounds s (candidateFreezingOuterExponent s a) hp
    (candidatePrimitivePhysicalOuterParameter_nonneg s a hp)
    (candidatePrimitivePhysicalOuterParameter_bound s a hp)

theorem candidatePrimitivePhysical_freezing_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + nativeMarkedFreezingExponent (s + 1) a) ^ nativeMarkedFreezingExponent (s + 1) a ≤
      (p + candidatePrimitivePhysicalBudgetExponent s a) ^
        candidatePrimitivePhysicalBudgetExponent s a :=
  (nativeMarkedFreezingPhysicalParameter_bounds hp
    (nativeMarkedFreezingExponent (s + 1) a)).2.1.trans
      (candidatePrimitivePhysicalScalarBounds s a hp).outer_budget

theorem candidatePrimitivePhysical_input_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + candidatePrimitivePhysicalBudgetExponent s a) ^
      candidatePrimitivePhysicalBudgetExponent s a :=
  (nativeMarkedFreezingPhysicalParameter_bounds hp
    (nativeMarkedFreezingExponent (s + 1) a)).1.trans
      (candidatePrimitivePhysicalScalarBounds s a hp).outer_budget

end Erdos3.VectorPolynomial

end

end OAI
