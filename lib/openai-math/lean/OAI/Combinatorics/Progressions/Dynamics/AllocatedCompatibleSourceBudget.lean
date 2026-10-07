import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonCover
import OAI.Combinatorics.Progressions.Polynomial.AllocatedCommonScalePolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCompatibleSourceLog {A : Type*} [Semiring A]
    (m : ℕ) (p c P e E : A) : A :=
  canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P + 1) +
    allocatedCommonSourceLog m p c P e (E + 5) + allocatedOriginalCoverAccuracy P (E + 1) + 4

theorem allocatedCompatibleSourceLog_bounds (m : ℕ) {p c P e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    let p₁ := allocatedCompatibleSourceLog m p c P e E
    0 ≤ p₁ ∧ p ≤ p₁ ∧ c ≤ p₁ ∧ P ≤ p₁ ∧
      allocatedRefinedPeriodLog m P + 1 ≤ p₁ ∧
      canonicalScalarSourceLog m (allocatedRefinedPeriodLog m P + 1) ≤ p₁ ∧
      allocatedCommonSourceLog m p c P e (E + 5) ≤ p₁ ∧
      allocatedCommonScaleLog m p c P e (E + 5) ≤ p₁ ∧
      allocatedCommonScaleNumeric m p c P (E + 5) ≤ p₁ ∧
      allocatedOriginalCoverAccuracy P (E + 1) + 4 ≤ p₁ := by
  have hE5 : 0 ≤ E + 5 := by linarith
  have hcut : 0 ≤ allocatedRefinedPeriodLog m P + 1 := by
    unfold allocatedRefinedPeriodLog
    positivity
  obtain ⟨hcanon, hcutcanon⟩ := canonicalScalarSourceLog_bounds m hcut
  obtain ⟨hscale, hcommon, hpcommon, hccommon, hPcommon, _, _, hscalecommon, hnumcommon⟩ :=
    allocatedCommonSourceLog_bounds m hp hc hP he hE5
  have haccuracy : 0 ≤ allocatedOriginalCoverAccuracy P (E + 1) := by
    have := coefficientErrorSpatialLog_nonneg hP
    unfold allocatedOriginalCoverAccuracy
    linarith
  dsimp only [allocatedCompatibleSourceLog]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
