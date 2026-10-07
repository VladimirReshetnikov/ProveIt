import OAI.Combinatorics.Progressions.Dynamics.AllocatedCommonCoarseBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCommonCoarseLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {s : ℝ}, 0 ≤ s →
      coarseSpatialReciprocalLog (allocatedCoarseInputEnvelope m dim s) ≤ (s + a) ^ a ∧
      coarseSpatialPartitionLog (allocatedCoarseInputEnvelope m dim s) ≤ (s + a) ^ a := by
  let poly : Polynomial ℕ :=
    coarseSpatialReciprocalLog (allocatedCoarseInputEnvelope m dim Polynomial.X) +
      coarseSpatialPartitionLog (allocatedCoarseInputEnvelope m dim Polynomial.X)
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro s hs
  let f : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) s
  have hearly (q : Polynomial ℕ) :
      f (allocatedCommonCoverEarlyLog m q q q q (q + 1)) =
        allocatedCommonCoverEarlyLog m (f q) (f q) (f q) (f q) (f q + 1) := by
    simp [map_ofNat, allocatedCommonCoverEarlyLog, allocatedComparisonDimension, allocatedSiteKernelMaskLog,
      allocatedCommonScaleNumeric, allocatedSiteScaleNumeric, allocatedReferenceIdealError,
      allocatedProfileGainLog, allocatedOriginalCoverAccuracy, profileReferenceErrorLog,
      coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog]
  have hrefined (q : Polynomial ℕ) :
      f (allocatedCommonRefinedSourceLog m q q q q q q) =
        allocatedCommonRefinedSourceLog m (f q) (f q) (f q) (f q) (f q) (f q) := by
    simp [map_ofNat, allocatedCommonRefinedSourceLog, allocatedRefinedPeriodLog,
      allocatedCommonSourceLog, allocatedCommonScaleLog, allocatedCommonScaleNumeric,
      allocatedSiteScaleNumeric, allocatedSiteKernelMaskLog, canonicalScalarSourceLog,
      allocatedReferenceIdealError, profileReferenceErrorLog, coefficientErrorSpatialLog,
      coefficientErrorVolumeLog, anisotropicSpatialCapLog, allocatedComparisonDimension,
      allocatedIdealScaleLog, allocatedIdealScaleInput, allocatedPhysicalIdealLengthEnvelope,
      allocatedTestLengthEnvelope, allocatedJointLengthEnvelope, allocatedTestEnvelope,
      allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
      allocatedKernelEnvelope, allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope,
      allocatedIdealRadiusEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
      allocatedSupportEnvelope, allocatedDensityEnvelope, kernelOutputEnvelope,
      kernelGeometryEnvelope, kernelInverseEnvelope]
  have hsource (q : Polynomial ℕ) :
      f (allocatedCoarseSourceEnvelope m q) = allocatedCoarseSourceEnvelope m (f q) := by
    dsimp only [allocatedCoarseSourceEnvelope]
    rw [hrefined, hearly]
  have hmass (q : Polynomial ℕ) :
      f (allocatedCoarseMassEnvelope m q) = allocatedCoarseMassEnvelope m (f q) := by
    simp [map_ofNat, allocatedCoarseMassEnvelope, coefficientMajorantMassLog,
      allocatedComparisonDimension, hsource, hearly]
  have hinput (q : Polynomial ℕ) :
      f (allocatedCoarseInputEnvelope m dim q) = allocatedCoarseInputEnvelope m dim (f q) := by
    simp [map_ofNat, allocatedCoarseInputEnvelope, allocatedCoarseMassBudget, anisotropicSpatialCapLog,
      spatialLipschitzEnvelope, spatialFixedProfileEnvelope, hmass]
  have hx : f Polynomial.X = s := by simp [f]
  have heval : poly.eval₂ (Nat.castRingHom ℝ) s =
      coarseSpatialReciprocalLog (allocatedCoarseInputEnvelope m dim s) +
        coarseSpatialPartitionLog (allocatedCoarseInputEnvelope m dim s) := by
    change f poly = _
    simp [map_ofNat, poly, coarseSpatialReciprocalLog, coarseSpatialPartitionLog,
      spatialTupleToleranceLog, hinput, hx]
  have hsum := hpoly s hs
  rw [heval] at hsum
  have hR : 0 ≤ s + (m + dim + 2 : ℕ) := by positivity
  have hcap := anisotropicSpatialCapLog_nonneg hR
  have hlip := (spatialCostEnvelopes_nonneg hR (le_refl (0 : ℝ))).2.2.2.2
  have hmass0 := allocatedCoarseMassBudget_nonneg m dim hs
  have hT : 0 ≤ allocatedCoarseInputEnvelope m dim s := by
    unfold allocatedCoarseInputEnvelope
    positivity
  obtain ⟨hinv, hpartition⟩ := coarseSpatialLogs_nonneg hT
  exact ⟨(le_add_of_nonneg_right hpartition).trans hsum,
    (le_add_of_nonneg_left hinv).trans hsum⟩

end Erdos3.VectorPolynomial

end

end OAI
