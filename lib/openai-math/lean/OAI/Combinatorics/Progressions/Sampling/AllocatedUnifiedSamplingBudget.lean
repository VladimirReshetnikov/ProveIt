import OAI.Combinatorics.Progressions.Estimates.AllocatedTupleSideThreshold

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedTupleErrorBudget (m : ℕ) (P p E : ℝ) : ℝ :=
  P + allocatedCoefficientAccuracyLog m p (E + 3)

noncomputable def allocatedUnifiedSamplingBudget (m dim A : ℕ) (P p E : ℝ) : ℝ :=
  allocatedScalarSamplingBudget m dim A P (allocatedTupleErrorBudget m P p E) +
    tupleWidthLogEnvelope p E + P + p + E + p * (p + 1)

theorem allocatedUnifiedSamplingBudget_bounds (m dim A : ℕ) {P p E : ℝ}
    (hP : 0 ≤ P) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Perr := allocatedTupleErrorBudget m P p E
    let Q := allocatedUnifiedSamplingBudget m dim A P p E
    0 ≤ Perr ∧ P ≤ Perr ∧ allocatedCoefficientAccuracyLog m p (E + 3) ≤ Perr ∧
      0 ≤ Q ∧ allocatedScalarSamplingBudget m dim A P Perr ≤ Q ∧
      tupleWidthLogEnvelope p E ≤ Q ∧ P + p ≤ Q ∧ p ≤ Q ∧ E ≤ Q ∧ p * (p + 1) ≤ Q := by
  have hacc : 0 ≤ allocatedCoefficientAccuracyLog m p (E + 3) := by
    have h := (allocatedCoefficientAccuracy_bounds m hp (by linarith : 0 ≤ E + 3)).2.1
    exact neg_nonpos.mp (Real.exp_le_one_iff.mp h)
  have herr : 0 ≤ allocatedTupleErrorBudget m P p E := add_nonneg hP hacc
  have hs := (allocatedScalarSamplingBudget_bounds m dim A hP herr).1
  have hw := (tupleLogEnvelopes_nonneg hp hE (le_refl (0 : ℝ))).2.1
  have hpp : 0 ≤ p * (p + 1) := by positivity
  dsimp only [allocatedTupleErrorBudget, allocatedUnifiedSamplingBudget] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem exists_allocatedUnifiedSamplingThreshold_bound (m dim A K : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P p E : ℝ}, 0 ≤ P → 0 ≤ p → 0 ≤ E →
      (allocatedUnifiedSamplingBudget m dim A P p E + K) ^ K ≤ (P + p + E + a) ^ a := by
  obtain ⟨c, _hc, hacc⟩ := exists_allocatedCoefficientAccuracyLog_bound m
  obtain ⟨b, _hb, hscalar⟩ := exists_allocatedScalarSamplingThreshold_bound m dim A 1
  let r : Polynomial ℕ := Polynomial.X + (Polynomial.X + 3 + Polynomial.C c) ^ c
  let poly : Polynomial ℕ :=
    ((r + Polynomial.C b) ^ b + tupleWidthLogEnvelope Polynomial.X Polynomial.X +
      Polynomial.X + Polynomial.X * (Polynomial.X + 1) + Polynomial.C K) ^ K
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P p E hP hp hE
  let R := P + p + E
  let rR := R + (R + 3 + c) ^ c
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hER : E ≤ R := by dsimp [R]; linarith
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hrr : 0 ≤ rR := by dsimp [rR]; positivity
  have hPr : P ≤ rR := hPR.trans (le_add_of_nonneg_right (by positivity))
  have hacc' : allocatedCoefficientAccuracyLog m p (E + 3) ≤ (R + 3 + c) ^ c := by
    apply (hacc hp (by linarith : 0 ≤ E + 3)).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [R]
    linarith
  have herrr : allocatedTupleErrorBudget m P p E ≤ rR := by
    unfold allocatedTupleErrorBudget
    exact add_le_add hPR hacc'
  have hbud := allocatedUnifiedSamplingBudget_bounds m dim A hP hp hE
  have hs := hscalar hP hbud.1 hPr herrr
  simp only [Nat.cast_one, pow_one] at hs
  have hwidth : tupleWidthLogEnvelope p E ≤ tupleWidthLogEnvelope R R := by
    dsimp only [tupleWidthLogEnvelope, tupleEarlyLogEnvelope, spatialTupleToleranceLog,
      spatialDisplacementEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog,
      coefficientErrorVolumeLog]
    gcongr
  have hprod : p * (p + 1) ≤ R * (R + 1) := by gcongr
  have hQ : allocatedUnifiedSamplingBudget m dim A P p E ≤
      (rR + b) ^ b + tupleWidthLogEnvelope R R + R + R * (R + 1) := by
    unfold allocatedUnifiedSamplingBudget
    dsimp only [R] at *
    linarith
  have hQ0 := hbud.2.2.2.1
  calc
    _ ≤ ((rR + b) ^ b + tupleWidthLogEnvelope R R + R + R * (R + 1) + K) ^ K :=
      pow_le_pow_left₀ (by positivity) (add_le_add hQ le_rfl) K
    _ ≤ _ := by
      simpa [poly, r, rR, R, tupleWidthLogEnvelope, tupleEarlyLogEnvelope, spatialTupleToleranceLog,
        spatialDisplacementEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog,
        coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI
