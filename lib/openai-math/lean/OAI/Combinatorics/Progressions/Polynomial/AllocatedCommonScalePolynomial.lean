import OAI.Combinatorics.Progressions.Dynamics.AllocatedCommonScaleBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedCommonSourceLog_mono (m : ℕ) {p c P e E p' c' P' e' E' : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hpp : p ≤ p') (hcc : c ≤ c') (hPP : P ≤ P') (hee : e ≤ e') (hEE : E ≤ E') :
    allocatedCommonSourceLog m p c P e E ≤ allocatedCommonSourceLog m p' c' P' e' E' := by
  have hP' : 0 ≤ P' := hP.trans hPP
  have hprofile : profileReferenceErrorLog P E ≤ profileReferenceErrorLog P' E' := by
    unfold profileReferenceErrorLog coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  have hnum : allocatedCommonScaleNumeric m p c P E ≤ allocatedCommonScaleNumeric m p' c' P' E' := by
    unfold allocatedCommonScaleNumeric allocatedSiteScaleNumeric
    gcongr
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  have hD' : 0 ≤ allocatedComparisonDimension m p' := hD.trans hDD
  have herror : allocatedReferenceIdealError m (allocatedComparisonDimension m p) P E ≤
      allocatedReferenceIdealError m (allocatedComparisonDimension m p') P' E' := by
    unfold allocatedReferenceIdealError
    gcongr
  have hw : allocatedSiteKernelMaskLog m P ≤ allocatedSiteKernelMaskLog m P' :=
    mul_le_mul_of_nonneg_left hPP (Nat.cast_nonneg _)
  have hlog := allocatedIdealScaleLog_mono m hD
    (allocatedCommonScaleNumeric_bounds m hp hc hP hE).1 he (allocatedSiteKernelMaskLog_nonneg m hP)
    (allocatedReferenceIdealError_nonneg m hD hP hE) hDD hnum hee hw herror
  have hsource : canonicalScalarSourceLog m P ≤ canonicalScalarSourceLog m P' := by
    unfold canonicalScalarSourceLog
    gcongr
  unfold allocatedCommonSourceLog
  exact add_le_add (add_le_add (add_le_add (add_le_add hsource hlog) hnum) hEE) le_rfl

theorem exists_allocatedCommonSourceLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p c P e E : ℝ}, 0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e → 0 ≤ E →
      allocatedCommonSourceLog m p c P e E ≤ (p + c + P + e + E + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonSourceLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p c P e E hp hc hP he hE
  have hmono := allocatedCommonSourceLog_mono m hp hc hP he hE
    (show p ≤ p + c + P + e + E by linarith)
    (show c ≤ p + c + P + e + E by linarith) (show P ≤ p + c + P + e + E by linarith)
    (show e ≤ p + c + P + e + E by linarith) (show E ≤ p + c + P + e + E by linarith)
  apply hmono.trans
  simpa [poly, allocatedCommonSourceLog, allocatedCommonScaleLog, allocatedCommonScaleNumeric,
    allocatedSiteScaleNumeric, allocatedSiteKernelMaskLog, canonicalScalarSourceLog,
    allocatedReferenceIdealError, profileReferenceErrorLog, coefficientErrorSpatialLog,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, allocatedComparisonDimension,
    allocatedIdealScaleLog, allocatedIdealScaleInput, allocatedPhysicalIdealLengthEnvelope,
    allocatedTestLengthEnvelope, allocatedJointLengthEnvelope, allocatedTestEnvelope,
    allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
    allocatedKernelEnvelope, allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope,
    allocatedIdealRadiusEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
    allocatedSupportEnvelope, allocatedDensityEnvelope, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow] using
    hbound (p + c + P + e + E) (by positivity)

end Erdos3.VectorPolynomial

end

end OAI
