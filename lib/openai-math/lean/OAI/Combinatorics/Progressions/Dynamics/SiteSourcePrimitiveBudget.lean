import OAI.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope

namespace OAI

section

namespace Erdos3

noncomputable def siteSourceParameter {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  canonicalScalarSourceLog m p + 4

noncomputable def siteSourceMaskLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (m * 2 ^ (m + 1) : ℕ) * siteSourceParameter m p

theorem siteSourceParameter_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ siteSourceParameter m p ∧ p ≤ siteSourceParameter m p ∧
      p + 4 ≤ siteSourceParameter m p ∧ canonicalScalarSourceLog m p ≤ siteSourceParameter m p := by
  obtain ⟨hC, hpC⟩ := canonicalScalarSourceLog_bounds m hp
  unfold siteSourceParameter
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem siteSourceMaskLog_nonneg (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ siteSourceMaskLog m p :=
  mul_nonneg (Nat.cast_nonneg _) (siteSourceParameter_bounds m hp).1

theorem exists_siteSourceParameter_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → siteSourceParameter m p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := siteSourceParameter m Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, siteSourceParameter, canonicalScalarSourceLog] using hbound p hp

theorem exists_siteSourceMaskLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → siteSourceMaskLog m p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := siteSourceMaskLog m Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, siteSourceMaskLog, siteSourceParameter, canonicalScalarSourceLog, Polynomial.eval₂_pow] using hbound p hp

theorem canonicalScalarSourceEnvelope_le_siteParameter (m : ℕ) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    canonicalScalarSourceEnvelope m M ≤ Real.exp (siteSourceParameter m p) :=
  (canonicalScalarSourceEnvelope_le_exp m hp hM).trans
    (Real.exp_le_exp.mpr (siteSourceParameter_bounds m hp).2.2.2)

end Erdos3

end

end OAI
