import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonCover
import OAI.Combinatorics.Progressions.Polynomial.AllocatedCommonScalePolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCommonRefinedSourceLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e Eraw Esite : A) : A :=
  canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P + 1) +
    allocatedCommonSourceLog m p c P e Eraw + 2 * p + Esite + 4

theorem allocatedCommonRefinedSourceLog_bounds (m : ℕ) {p c P e Eraw Esite : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hEraw : 0 ≤ Eraw) (hEsite : 0 ≤ Esite) :
    let Q := allocatedCommonRefinedSourceLog m p c P e Eraw Esite
    0 ≤ Q ∧ p ≤ Q ∧ 2 * p ≤ Q ∧ c ≤ Q ∧ P ≤ Q ∧ Esite + 4 ≤ Q ∧
      allocatedRefinedPeriodLog m P + 1 ≤ Q ∧
      canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P + 1) ≤ Q ∧
      allocatedCommonScaleLog m p c P e Eraw ≤ Q ∧
      allocatedCommonScaleNumeric m p c P Eraw ≤ Q ∧ Eraw + 4 ≤ Q := by
  have hlog : 0 ≤ allocatedRefinedPeriodLog m P + 1 := by
    unfold allocatedRefinedPeriodLog
    positivity
  obtain ⟨hcanon, hlogCanon⟩ := canonicalScalarSourceLog_bounds m hlog
  obtain ⟨hscale, hbase, hpBase, hcBase, hPBase, hRawBase, _, hscaleBase, hnumBase⟩ :=
    allocatedCommonSourceLog_bounds m hp hc hP he hEraw
  dsimp only [allocatedCommonRefinedSourceLog]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem allocatedCommonRefinedSourceLog_mono (m : ℕ)
    {p c P e Eraw Esite p' c' P' e' Eraw' Esite' : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e)
    (hEraw : 0 ≤ Eraw)
    (hpp : p ≤ p') (hcc : c ≤ c') (hPP : P ≤ P') (hee : e ≤ e')
    (hRaw : Eraw ≤ Eraw') (hSite : Esite ≤ Esite') :
    allocatedCommonRefinedSourceLog m p c P e Eraw Esite ≤
      allocatedCommonRefinedSourceLog m p' c' P' e' Eraw' Esite' := by
  have hcanon : canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P + 1) ≤
      canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P' + 1) := by
    unfold canonicalScalarSourceLog allocatedRefinedPeriodLog
    gcongr
  have hbase := allocatedCommonSourceLog_mono m hp hc hP he hEraw hpp hcc hPP hee hRaw
  unfold allocatedCommonRefinedSourceLog
  linarith

theorem exists_allocatedCommonRefinedSourceLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p c P e Eraw Esite : ℝ},
      0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e → 0 ≤ Eraw → 0 ≤ Esite →
      allocatedCommonRefinedSourceLog m p c P e Eraw Esite ≤
        (p + c + P + e + Eraw + Esite + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonRefinedSourceLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p c P e Eraw Esite hp hc hP he hEraw hEsite
  have hmono := allocatedCommonRefinedSourceLog_mono m hp hc hP he hEraw
    (show p ≤ p + c + P + e + Eraw + Esite by linarith)
    (show c ≤ p + c + P + e + Eraw + Esite by linarith)
    (show P ≤ p + c + P + e + Eraw + Esite by linarith)
    (show e ≤ p + c + P + e + Eraw + Esite by linarith)
    (show Eraw ≤ p + c + P + e + Eraw + Esite by linarith)
    (show Esite ≤ p + c + P + e + Eraw + Esite by linarith)
  apply hmono.trans
  simpa [poly, allocatedCommonRefinedSourceLog, allocatedRefinedPeriodLog,
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
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow] using
    hbound (p + c + P + e + Eraw + Esite) (by positivity)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCommonCoverEarlyLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e E : A) : A :=
  let D := allocatedComparisonDimension m p
  let w := allocatedSiteKernelMaskLog m P
  8 + p + c + P + e + E + D + allocatedCommonScaleNumeric m p c P (E + 1 + 4) + w +
    allocatedReferenceIdealError m D P (E + 1 + 4) + allocatedProfileGainLog m D P w +
    allocatedOriginalCoverAccuracy P (E + 1)

theorem allocatedCommonCoverEarlyLog_bounds (m : ℕ) {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    let q := allocatedCommonCoverEarlyLog m p c P e E
    let D := allocatedComparisonDimension m p
    let w := allocatedSiteKernelMaskLog m P
    1 ≤ q ∧ p ≤ q ∧ c ≤ q ∧ P ≤ q ∧ e ≤ q ∧ E + 1 + 4 ≤ q ∧ D ≤ q ∧
      allocatedCommonScaleNumeric m p c P (E + 1 + 4) ≤ q ∧ w ≤ q ∧
      allocatedReferenceIdealError m D P (E + 1 + 4) ≤ q ∧
      allocatedProfileGainLog m D P w ≤ q ∧ allocatedOriginalCoverAccuracy P (E + 1) ≤ q := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have hnum := (allocatedCommonScaleNumeric_bounds m hp hc hP (by linarith : 0 ≤ E + 1 + 4)).1
  have herr := allocatedReferenceIdealError_nonneg m hD hP (by linarith : 0 ≤ E + 1 + 4)
  have hgain := allocatedProfileGainLog_nonneg m hD hP hw
  have hsite : 0 ≤ allocatedOriginalCoverAccuracy P (E + 1) := by
    have h := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  dsimp only [allocatedCommonCoverEarlyLog]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem allocatedCommonCoverEarlyLog_mono (m : ℕ) {p c P e E p' c' P' e' E' : ℝ}
    (hp : 0 ≤ p) (_hc : 0 ≤ c) (hP : 0 ≤ P) (_he : 0 ≤ e) (_hE : 0 ≤ E)
    (hpp : p ≤ p') (hcc : c ≤ c') (hPP : P ≤ P') (hee : e ≤ e') (hEE : E ≤ E') :
    allocatedCommonCoverEarlyLog m p c P e E ≤ allocatedCommonCoverEarlyLog m p' c' P' e' E' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  have hD' : 0 ≤ allocatedComparisonDimension m p' := hD.trans hDD
  have hP' : 0 ≤ P' := hP.trans hPP
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have hww : allocatedSiteKernelMaskLog m P ≤ allocatedSiteKernelMaskLog m P' := by
    unfold allocatedSiteKernelMaskLog
    gcongr
  have hnum : allocatedCommonScaleNumeric m p c P (E + 1 + 4) ≤
      allocatedCommonScaleNumeric m p' c' P' (E' + 1 + 4) := by
    unfold allocatedCommonScaleNumeric allocatedSiteScaleNumeric profileReferenceErrorLog
      coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  have herr : allocatedReferenceIdealError m (allocatedComparisonDimension m p) P (E + 1 + 4) ≤
      allocatedReferenceIdealError m (allocatedComparisonDimension m p') P' (E' + 1 + 4) := by
    unfold allocatedReferenceIdealError profileReferenceErrorLog coefficientErrorSpatialLog
      coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  have hgain : allocatedProfileGainLog m (allocatedComparisonDimension m p) P
      (allocatedSiteKernelMaskLog m P) ≤ allocatedProfileGainLog m (allocatedComparisonDimension m p') P'
        (allocatedSiteKernelMaskLog m P') := by
    unfold allocatedProfileGainLog
    gcongr
  have hsite : allocatedOriginalCoverAccuracy P (E + 1) ≤ allocatedOriginalCoverAccuracy P' (E' + 1) := by
    unfold allocatedOriginalCoverAccuracy coefficientErrorSpatialLog coefficientErrorVolumeLog
      anisotropicSpatialCapLog
    gcongr
  unfold allocatedCommonCoverEarlyLog
  linarith

theorem exists_allocatedCommonCoverEarlyLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p c P e E : ℝ},
      0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e → 0 ≤ E →
      allocatedCommonCoverEarlyLog m p c P e E ≤ (p + c + P + e + E + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonCoverEarlyLog m
    Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p c P e E hp hc hP he hE
  have hmono := allocatedCommonCoverEarlyLog_mono m hp hc hP he hE
    (show p ≤ p + c + P + e + E by linarith)
    (show c ≤ p + c + P + e + E by linarith)
    (show P ≤ p + c + P + e + E by linarith)
    (show e ≤ p + c + P + e + E by linarith)
    (show E ≤ p + c + P + e + E by linarith)
  apply hmono.trans
  simpa [poly, allocatedCommonCoverEarlyLog, allocatedComparisonDimension, allocatedSiteKernelMaskLog,
    allocatedCommonScaleNumeric, allocatedSiteScaleNumeric, allocatedReferenceIdealError,
    allocatedProfileGainLog, allocatedOriginalCoverAccuracy, profileReferenceErrorLog,
    coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
    Polynomial.eval₂_pow] using hbound (p + c + P + e + E) (by positivity)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators NNReal

noncomputable def coarseProfileConstant : ℕ := ⌈30 / smoothProbabilityProfile 0⌉₊ + 1

noncomputable def allocatedCommonCoarseSourceLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e E : A) : A :=
  allocatedCommonRefinedSourceLog m p c P e ((E + 1) + 1 + 4)
    (allocatedOriginalCoverAccuracy P ((E + 1) + 1))

noncomputable def allocatedCommonCoarseMassLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e E : A) : A :=
  let u := allocatedCommonCoarseSourceLog m p c P e E
  allocatedSiteSpatialMassLog (allocatedComparisonDimension m u)
    (allocatedSiteKernelMaskLog m P) (allocatedIdealProfileLog m u e)

noncomputable def allocatedCommonCoarseMass (m dim : ℕ) (X : Type*) [Fintype X]
    (p c P e E : ℝ) : ℝ :=
  (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
    ((p + 1) ^ dim) ^ Fintype.card X *
    Real.exp (allocatedCommonCoarseMassLog m p c P e E + 1) * 2

noncomputable def allocatedCommonCoarseMesh (m : ℕ) {dim : ℕ} {G : Type*} [Fintype G]
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ)
    (p c P e E : ℝ) : ℝ :=
  allocatedRecenteredCoarseMesh (M := M) X modulus selection (allocatedPrimitiveRootRatio p)
    (allocatedCommonCoarseMass m dim X p c P e E) (normalizedSpatialShare E)

noncomputable def allocatedCoarseSourceEnvelope {A : Type*} [Semiring A] (m : ℕ) (s : A) : A :=
  let q := allocatedCommonCoverEarlyLog m s s s s (s + 1)
  allocatedCommonRefinedSourceLog m q q q q q q

noncomputable def allocatedCoarseMassEnvelope {A : Type*} [Semiring A] (m : ℕ) (s : A) : A :=
  let q := allocatedCommonCoverEarlyLog m s s s s (s + 1)
  let u := allocatedCoarseSourceEnvelope m s
  let D := allocatedComparisonDimension m u
  coefficientMajorantMassLog D + D * q + D * (u + q)

noncomputable def allocatedCoarseMassBudget {A : Type*} [Semiring A] (m dim : ℕ) (s : A) : A :=
  (coarseProfileConstant : ℕ) * (dim + 1 : ℕ) * s +
    (dim : ℕ) * (s + (m + dim + 2 : ℕ)) * s + allocatedCoarseMassEnvelope m s + 2

noncomputable def allocatedCoarseInputEnvelope {A : Type*} [Semiring A] (m dim : ℕ) (s : A) : A :=
  let R := s + (m + dim + 2 : ℕ)
  2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
    allocatedCoarseMassBudget m dim s + 4

theorem allocatedCommonCoarseSourceLog_nonneg (m : ℕ) {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    0 ≤ allocatedCommonCoarseSourceLog m p c P e E := by
  have hsite : 0 ≤ allocatedOriginalCoverAccuracy P ((E + 1) + 1) := by
    have h := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  exact (allocatedCommonRefinedSourceLog_bounds m hp hc hP he (by linarith) hsite).1

theorem allocatedCommonCoarseEnvelope_bounds (m : ℕ) {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    let s := p + c + P + e + E
    0 ≤ allocatedCoarseSourceEnvelope m s ∧
      allocatedCommonCoarseSourceLog m p c P e E ≤ allocatedCoarseSourceEnvelope m s ∧
      0 ≤ allocatedCommonCoarseMassLog m p c P e E ∧
      allocatedCommonCoarseMassLog m p c P e E ≤ allocatedCoarseMassEnvelope m s ∧
      0 ≤ allocatedCoarseMassEnvelope m s := by
  intro s
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let q := allocatedCommonCoverEarlyLog m s s s s (s + 1)
  have hq : 0 ≤ q := zero_le_one.trans
    (allocatedCommonCoverEarlyLog_bounds m hs hs hs hs (by linarith : 0 ≤ s + 1)).1
  have hqq : allocatedCommonCoverEarlyLog m p c P e (E + 1) ≤ q := by
    apply allocatedCommonCoverEarlyLog_mono m hp hc hP he (by linarith)
    all_goals dsimp only [s]; linarith
  obtain ⟨_, hpq, hcq, hPq, heq, hrawq, _, _, hwq, _, _, hsiteq⟩ :=
    allocatedCommonCoverEarlyLog_bounds m hp hc hP he (show 0 ≤ E + 1 by linarith)
  have hu : 0 ≤ allocatedCoarseSourceEnvelope m s :=
    (allocatedCommonRefinedSourceLog_bounds m hq hq hq hq hq hq).1
  have hsource := allocatedCommonCoarseSourceLog_nonneg m hp hc hP he hE
  have hsourceu : allocatedCommonCoarseSourceLog m p c P e E ≤ allocatedCoarseSourceEnvelope m s := by
    exact allocatedCommonRefinedSourceLog_mono m hp hc hP he (by linarith)
      (hpq.trans hqq) (hcq.trans hqq) (hPq.trans hqq) (heq.trans hqq)
      (hrawq.trans hqq) (hsiteq.trans hqq)
  have hD := (allocatedComparisonDimension_bounds m hsource).1
  have hDu := (allocatedComparisonDimension_bounds m hu).1
  have hDD := allocatedComparisonDimension_mono m hsource hsourceu
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have hwm : allocatedSiteKernelMaskLog m P ≤ q := hwq.trans hqq
  have hem : e ≤ q := heq.trans hqq
  have hmass : 0 ≤ allocatedCommonCoarseMassLog m p c P e E :=
    allocatedSiteSpatialMassLog_nonneg hD hw (allocatedIdealProfileLog_nonneg m hsource he)
  have hmassBound : allocatedCommonCoarseMassLog m p c P e E ≤ allocatedCoarseMassEnvelope m s := by
    have hbase : coefficientMajorantMassLog
        (allocatedComparisonDimension m (allocatedCommonCoarseSourceLog m p c P e E)) ≤
        coefficientMajorantMassLog (allocatedComparisonDimension m (allocatedCoarseSourceEnvelope m s)) := by
      unfold coefficientMajorantMassLog
      gcongr
    exact add_le_add (add_le_add hbase (mul_le_mul hDD hwm hw hDu))
      (mul_le_mul hDD (add_le_add hsourceu hem) (add_nonneg hsource he) hDu)
  exact ⟨hu, hsourceu, hmass, hmassBound, hmass.trans hmassBound⟩

theorem allocatedCommonCoarseMass_nonneg (m dim : ℕ) (X : Type*) [Fintype X]
    {p c P e E : ℝ} (hp : 0 ≤ p) : 0 ≤ allocatedCommonCoarseMass m dim X p c P e E := by
  have hf := smoothProbabilityProfile_pos_zero
  unfold allocatedCommonCoarseMass
  positivity

theorem allocatedCoarseMassBudget_nonneg (m dim : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ allocatedCoarseMassBudget m dim s := by
  have h := (allocatedCommonCoarseEnvelope_bounds m hs (le_refl 0) (le_refl 0)
    (le_refl 0) (le_refl 0)).2.2.2.2
  simp only [add_zero] at h
  unfold allocatedCoarseMassBudget
  positivity

theorem allocatedCommonCoarseMass_le_exp (m dim : ℕ) (X : Type*) [Fintype X]
    {p c P e E : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hX : (Fintype.card X : ℝ) ≤ P) :
    allocatedCommonCoarseMass m dim X p c P e E ≤
      Real.exp (allocatedCoarseMassBudget m dim (p + c + P + e + E)) := by
  let s := p + c + P + e + E
  let R := s + (m + dim + 2 : ℕ)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hXs : (Fintype.card X : ℝ) ≤ s := hX.trans (by dsimp [s]; linarith)
  have hcount : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ (dim + 1 : ℕ) * s := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hXs (Nat.cast_nonneg _)
  have hbase0 : 0 ≤ 30 / smoothProbabilityProfile 0 := div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le
  have hbase : 30 / smoothProbabilityProfile 0 ≤ Real.exp (coarseProfileConstant : ℝ) := by
    have hceil : 30 / smoothProbabilityProfile 0 ≤ (coarseProfileConstant : ℝ) := by
      unfold coarseProfileConstant
      push_cast
      linarith [Nat.le_ceil (30 / smoothProbabilityProfile 0)]
    exact hceil.trans (by linarith [Real.add_one_le_exp (coarseProfileConstant : ℝ)])
  have hfirst := pow_le_exp_mul_of_le_exp hbase0 hbase (Nat.cast_nonneg coarseProfileConstant)
    (Fintype.card (Option (Fin dim) × X)) hcount
  have hpR : p + 1 ≤ R := by dsimp [R, s]; push_cast; linarith
  have hpExp : p + 1 ≤ Real.exp R := hpR.trans (by linarith [Real.add_one_le_exp R])
  have hinner := pow_le_exp_mul_of_le_exp (show 0 ≤ p + 1 by linarith) hpExp hR dim (le_refl (dim : ℝ))
  have hsecond := pow_le_exp_mul_of_le_exp (pow_nonneg (show 0 ≤ p + 1 by linarith) dim)
    hinner (mul_nonneg (Nat.cast_nonneg dim) hR) (Fintype.card X) hXs
  have hmass := (allocatedCommonCoarseEnvelope_bounds m hp hc hP he hE).2.2.2.1
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  unfold allocatedCommonCoarseMass
  calc
    _ ≤ Real.exp (((dim + 1 : ℕ) * s) * (coarseProfileConstant : ℝ)) *
        Real.exp (s * ((dim : ℝ) * R)) * Real.exp (allocatedCoarseMassEnvelope m s + 1) * Real.exp 1 := by
      gcongr
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      unfold allocatedCoarseMassBudget
      dsimp only [R, s]
      ring

end Erdos3.VectorPolynomial

end

end OAI
