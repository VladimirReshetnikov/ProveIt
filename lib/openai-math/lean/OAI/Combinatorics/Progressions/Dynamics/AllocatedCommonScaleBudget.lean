import OAI.Combinatorics.Progressions.Estimates.CanonicalSiteBlocks

namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedCommonScaleNumeric {A : Type*} [Semiring A]
    (m : ℕ) (p c P E : A) : A :=
  allocatedSiteScaleNumeric m p + c + P +
    ((m + 1 : ℕ) * P + P ^ 2 + (m + 2 : ℕ)) + profileReferenceErrorLog P E

noncomputable def allocatedCommonScaleLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e E : A) : A :=
  allocatedIdealScaleLog m (allocatedComparisonDimension m p)
    (allocatedCommonScaleNumeric m p c P E) e (allocatedSiteKernelMaskLog m P)
    (allocatedReferenceIdealError m (allocatedComparisonDimension m p) P E)

noncomputable def allocatedCommonSourceLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e E : A) : A :=
  canonicalScalarSourceLog m P + allocatedCommonScaleLog m p c P e E +
    allocatedCommonScaleNumeric m p c P E + E + 4

theorem allocatedCommonScaleNumeric_bounds (m : ℕ) {p c P E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    let q := allocatedCommonScaleNumeric m p c P E
    0 ≤ q ∧ p ≤ q ∧ c ≤ q ∧ P ≤ q ∧ allocatedSiteScaleNumeric m p ≤ q ∧
      profileReferenceErrorLog P E ≤ q ∧
      (m + 1 : ℕ) * P + P ^ 2 + (m + 2 : ℕ) ≤ q := by
  obtain ⟨hs, hps, _⟩ := allocatedSiteScaleNumeric_bounds m hp
  have he : 0 ≤ profileReferenceErrorLog P E := by
    have hc := coefficientErrorSpatialLog_nonneg hP
    unfold profileReferenceErrorLog
    linarith
  have hr : 0 ≤ (m + 1 : ℕ) * P + P ^ 2 + (m + 2 : ℕ) := by positivity
  dsimp only [allocatedCommonScaleNumeric]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem allocatedCommonSourceLog_bounds (m : ℕ) {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    0 ≤ allocatedCommonScaleLog m p c P e E ∧
    0 ≤ allocatedCommonSourceLog m p c P e E ∧
    p ≤ allocatedCommonSourceLog m p c P e E ∧
    c ≤ allocatedCommonSourceLog m p c P e E ∧
    P ≤ allocatedCommonSourceLog m p c P e E ∧
    E + 4 ≤ allocatedCommonSourceLog m p c P e E ∧
    canonicalScalarSourceLog m P ≤ allocatedCommonSourceLog m p c P e E ∧
    allocatedCommonScaleLog m p c P e E ≤ allocatedCommonSourceLog m p c P e E ∧
    allocatedCommonScaleNumeric m p c P E ≤ allocatedCommonSourceLog m p c P e E := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  obtain ⟨hq, hpq, hcq, hPq, _⟩ := allocatedCommonScaleNumeric_bounds m hp hc hP hE
  have hw := allocatedSiteKernelMaskLog_nonneg m hP
  have herr := allocatedReferenceIdealError_nonneg m hD hP hE
  obtain ⟨_, hQ, _, _, _, hQL⟩ := allocatedIdealScaleInput_bounds m hD hq he hw herr
  have hL : 0 ≤ allocatedCommonScaleLog m p c P e E := hQ.trans hQL
  have hC := (canonicalScalarSourceLog_bounds m hP).1
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold allocatedCommonSourceLog; linarith

end Erdos3.VectorPolynomial

end

end OAI
