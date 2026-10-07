import OAI.Combinatorics.Progressions.Estimates.AllocatedInactiveJointSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedMixedPointCapLog {A : Type*} [Semiring A] (m : ℕ) (D p v : A) : A :=
  allocatedActivePointCapLog m D p + allocatedInactivePointCapLog m D p v

def allocatedMixedSiteOutputLog {A : Type*} [Semiring A] (m : ℕ) (D p v E : A) : A :=
  allocatedActiveSiteOutputLog m D p E + allocatedInactiveSiteOutputLog m D p v E

def allocatedMixedAccuracyLog {A : Type*} [Semiring A] (m : ℕ) (D p v E : A) : A :=
  uniformProductAccuracyLog D (allocatedMixedPointCapLog m D p v) E + 1

def allocatedMixedJointSiteLog {A : Type*} [Semiring A] (m : ℕ) (D p v E : A) : A :=
  allocatedMixedSiteOutputLog m D p v (allocatedMixedAccuracyLog m D p v E)

noncomputable def allocatedMixedJointPrimitiveLog {A : Type*} [Semiring A] (m : ℕ) (p v E : A) : A :=
  allocatedMixedJointSiteLog m (allocatedComparisonDimension m p) p v E

theorem allocatedMixedPointCapLog_bounds (m : ℕ) {D p v : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ allocatedMixedPointCapLog m D p v ∧
      allocatedActivePointCapLog m D p ≤ allocatedMixedPointCapLog m D p v ∧
      allocatedInactivePointCapLog m D p v ≤ allocatedMixedPointCapLog m D p v := by
  have hA := allocatedActivePointCapLog_nonneg m hD hp
  have hI := allocatedInactivePointCapLog_nonneg m hD hp hv
  unfold allocatedMixedPointCapLog
  exact ⟨by positivity, by linarith, by linarith⟩

theorem allocatedMixedSiteOutputLog_bounds (m : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedMixedSiteOutputLog m D p v E ∧
      allocatedActiveSiteOutputLog m D p E ≤ allocatedMixedSiteOutputLog m D p v E ∧
      allocatedInactiveSiteOutputLog m D p v E ≤ allocatedMixedSiteOutputLog m D p v E := by
  have hA := allocatedActiveSiteOutputLog_nonneg m hD hp hE
  have hI := (allocatedInactiveSiteOutputLog_bounds m hD hp hv hE).1
  unfold allocatedMixedSiteOutputLog
  exact ⟨by positivity, by linarith, by linarith⟩

theorem allocatedMixedJointLogs_nonneg (m : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedMixedAccuracyLog m D p v E ∧ 0 ≤ allocatedMixedJointSiteLog m D p v E := by
  have hT := (allocatedMixedPointCapLog_bounds m hD hp hv).1
  have hU := uniformProductAccuracyLog_nonneg hD hT hE
  have hA : 0 ≤ allocatedMixedAccuracyLog m D p v E := by
    unfold allocatedMixedAccuracyLog
    positivity
  exact ⟨hA, (allocatedMixedSiteOutputLog_bounds m hD hp hv hA).1⟩

theorem allocatedActiveSiteOutputLog_eval (m : ℕ) (D p E : Polynomial ℕ) (x : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) x (allocatedActiveSiteOutputLog m D p E) =
      allocatedActiveSiteOutputLog m (Polynomial.eval₂ (Nat.castRingHom ℝ) x D)
        (Polynomial.eval₂ (Nat.castRingHom ℝ) x p) (Polynomial.eval₂ (Nat.castRingHom ℝ) x E) := by
  simp [allocatedActiveSiteOutputLog, siteExponentialOutputLog, allocatedActiveSiteBudgetLog,
    allocatedActiveSpectrumLog, allocatedActivePointCapLog, allocatedSpectrumCardEnvelope,
    allocatedGridTorusLog, allocatedSpectrumScaleLog, positiveRetainedComplexityLog,
    positiveRetainedDenominatorLog, positiveSpectrumCardLog, positiveRetainedFrequencyLog,
    positiveRetainedBiasLog, positiveModerateAccuracyLog, positiveModerateSpectrumLog,
    positiveModerateCoverLog, positiveModerateLengthLog, allocatedNaturalSiteLog,
    majorArcCoverLog, majorArcLengthLog, majorArcBiasLog, majorArcErrorLog,
    majorArcLocalizationLog, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow]

theorem allocatedInactiveSiteOutputLog_eval (m : ℕ) (D p v E : Polynomial ℕ) (x : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) x (allocatedInactiveSiteOutputLog m D p v E) =
      allocatedInactiveSiteOutputLog m (Polynomial.eval₂ (Nat.castRingHom ℝ) x D)
        (Polynomial.eval₂ (Nat.castRingHom ℝ) x p) (Polynomial.eval₂ (Nat.castRingHom ℝ) x v)
        (Polynomial.eval₂ (Nat.castRingHom ℝ) x E) := by
  simp [allocatedInactiveSiteOutputLog, allocatedInactiveSiteBudgetLog,
    inactiveShortLipschitzLog, inactiveShortScaleLog, allocatedInactiveSupportLog,
    allocatedInactiveSpectrumLog, allocatedInactiveTorusLog, allocatedInactiveScaleLog,
    uniformRetainedComplexityLog, uniformSpectrumSizeLog, uniformSpectrumCardLog,
    uniformRetainedFrequencyLog, uniformRetainedDenominatorLog, uniformRetainedBiasLog,
    uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog, majorArcLengthLog,
    majorArcBiasLog, majorArcErrorLog, majorArcLocalizationLog,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow]

theorem allocatedMixedPointCapLog_eval (m : ℕ) (D p v : Polynomial ℕ) (x : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) x (allocatedMixedPointCapLog m D p v) =
      allocatedMixedPointCapLog m (Polynomial.eval₂ (Nat.castRingHom ℝ) x D)
        (Polynomial.eval₂ (Nat.castRingHom ℝ) x p) (Polynomial.eval₂ (Nat.castRingHom ℝ) x v) := by
  simp [allocatedMixedPointCapLog, allocatedActivePointCapLog, allocatedInactivePointCapLog,
    allocatedSpectrumCardEnvelope, allocatedGridTorusLog, allocatedSpectrumScaleLog,
    positiveSpectrumCardLog, positiveRetainedBiasLog, positiveModerateAccuracyLog,
    positiveModerateSpectrumLog, positiveModerateCoverLog, positiveModerateLengthLog,
    inactiveShortCapLog, inactiveShortScaleLog, allocatedInactiveSpectrumLog,
    allocatedInactiveTorusLog, allocatedInactiveScaleLog, uniformRetainedComplexityLog,
    uniformSpectrumSizeLog, uniformSpectrumCardLog, uniformRetainedFrequencyLog,
    uniformRetainedDenominatorLog, uniformRetainedBiasLog, uniformBlockAccuracyLog,
    majorArcSpectrumLog, majorArcCoverLog, majorArcLengthLog, majorArcBiasLog,
    majorArcErrorLog, majorArcLocalizationLog, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow]

theorem exists_allocatedMixedJointPrimitiveLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedMixedJointPrimitiveLog m p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedMixedJointPrimitiveLog m Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedMixedJointPrimitiveLog, allocatedMixedJointSiteLog,
    allocatedMixedSiteOutputLog, allocatedMixedAccuracyLog, uniformProductAccuracyLog,
    allocatedActiveSiteOutputLog_eval, allocatedInactiveSiteOutputLog_eval,
    allocatedMixedPointCapLog_eval, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.VectorPolynomial

end

end OAI
