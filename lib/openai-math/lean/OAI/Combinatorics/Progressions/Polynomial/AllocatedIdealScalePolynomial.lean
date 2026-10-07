import OAI.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedPhysicalIdealLengthEnvelope_mono (m : ℕ)
    {D p e w E D' p' e' w' E' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w)
    (hDD : D ≤ D') (hpp : p ≤ p') (hee : e ≤ e') (hww : w ≤ w') (hEE : E ≤ E') :
    allocatedPhysicalIdealLengthEnvelope m D p e w E ≤
      allocatedPhysicalIdealLengthEnvelope m D' p' e' w' E' := by
  have hD' := hD.trans hDD
  have hp' := hp.trans hpp
  have he' := he.trans hee
  have hw' := hw.trans hww
  have ho := kernelOutputEnvelope_mono hD (show 0 ≤ 4 * (p + 8) by positivity)
    hDD (show 4 * (p + 8) ≤ 4 * (p' + 8) by linarith)
  have hd : allocatedDensityEnvelope m D p ≤ allocatedDensityEnvelope m D' p' := by
    unfold allocatedDensityEnvelope
    gcongr
  have hd0 := allocatedDensityEnvelope_nonneg m hD hp
  have hs : allocatedSupportEnvelope m D p ≤ allocatedSupportEnvelope m D' p' := by
    unfold allocatedSupportEnvelope
    gcongr
  have hs0 := allocatedSupportEnvelope_nonneg m hD hp
  have ht : allocatedTestEnvelope m D p (E + 3) ≤ allocatedTestEnvelope m D' p' (E' + 3) := by
    unfold allocatedTestEnvelope
    gcongr
  have hlength := allocatedJointLengthEnvelope_mono m hD hp hDD hpp ht
  have hg : allocatedIdealGridEnvelope m D p e ≤ allocatedIdealGridEnvelope m D' p' e' := by
    unfold allocatedIdealGridEnvelope allocatedIdealRadiusEnvelope
      allocatedProxyLipEnvelope allocatedIdealLipEnvelope
    gcongr
  have hg0 := allocatedIdealGridEnvelope_nonneg m hD hp he
  have hmesh : allocatedIdealMeshEnvelope m D p e ≤ allocatedIdealMeshEnvelope m D' p' e' := by
    unfold allocatedIdealMeshEnvelope
    gcongr
  unfold allocatedPhysicalIdealLengthEnvelope allocatedTestLengthEnvelope
  gcongr

theorem allocatedIdealScaleLog_mono (m : ℕ) {D p e w E D' p' e' w' E' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hDD : D ≤ D') (hpp : p ≤ p') (hee : e ≤ e') (hww : w ≤ w') (hEE : E ≤ E') :
    allocatedIdealScaleLog m D p e w E ≤ allocatedIdealScaleLog m D' p' e' w' E' := by
  have hlength := allocatedPhysicalIdealLengthEnvelope_mono m hD hp he hw hDD hpp hee hww hEE
  have hQ : allocatedIdealScaleInput m D p e w E ≤ allocatedIdealScaleInput m D' p' e' w' E' := by
    unfold allocatedIdealScaleInput
    gcongr
  have hQ0 := (allocatedIdealScaleInput_bounds m hD hp he hw hE).2.1
  dsimp only [allocatedIdealScaleLog]
  gcongr

theorem exists_allocatedIdealScaleLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {D p e w E : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ e → 0 ≤ w → 0 ≤ E →
      allocatedIdealScaleLog m D p e w E ≤ (D + p + e + w + E + a) ^ a := by
  let poly : Polynomial ℕ := allocatedIdealScaleLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro D p e w E hD hp he hw hE
  have hmono := allocatedIdealScaleLog_mono m hD hp he hw hE
    (show D ≤ D + p + e + w + E by linarith)
    (show p ≤ D + p + e + w + E by linarith)
    (show e ≤ D + p + e + w + E by linarith)
    (show w ≤ D + p + e + w + E by linarith)
    (show E ≤ D + p + e + w + E by linarith)
  apply hmono.trans
  simpa [poly, allocatedIdealScaleLog, allocatedIdealScaleInput,
    allocatedPhysicalIdealLengthEnvelope, allocatedTestLengthEnvelope,
    allocatedJointLengthEnvelope, allocatedTestEnvelope, allocatedFrontEnvelope,
    allocatedAccuracyEnvelope, allocatedTupleEnvelope, allocatedKernelEnvelope,
    allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope, allocatedIdealRadiusEnvelope,
    allocatedProxyLipEnvelope, allocatedIdealLipEnvelope, allocatedSupportEnvelope,
    allocatedDensityEnvelope, kernelOutputEnvelope, kernelGeometryEnvelope,
    kernelInverseEnvelope, Polynomial.eval₂_pow] using hbound (D + p + e + w + E) (by positivity)

end Erdos3.VectorPolynomial

end

end OAI
