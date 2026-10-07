import OAI.Combinatorics.Progressions.Estimates.ApproxMomentEnvelope

namespace OAI

section

namespace Erdos3

theorem approxMomentBudget_eta_le_half (N r q : ℕ) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) : eta ≤ 1 / 2 := by
  have hpow : 1 ≤ approxMomentEnvelope N r M ^ q := one_le_pow₀ (approxMomentEnvelope_one_le N r hM)
  have h : eta ≤ eta * approxMomentEnvelope N r M ^ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow heta
  exact h.trans hbudget

theorem approxMomentBudget_mono (N q : ℕ) {s r : ℕ} (hsr : s ≤ r) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) :
    eta * approxMomentEnvelope N s M ^ q ≤ 1 / 2 := by
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (zero_le_one.trans (approxMomentEnvelope_one_le N s hM))
    (approxMomentEnvelope_mono N hsr hM) q) heta).trans hbudget

theorem approxMomentBudget_error_le_one (N q : ℕ) {k r : ℕ} (hkr : k ≤ r) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) :
    eta * ((2 : ℝ) ^ k * (N : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1 := by
  have he := approxMomentBudget_eta_le_half N r q hM heta hbudget
  have hterm := (approxMomentEnvelope_bounds_term N k hM (by linarith : eta ≤ 1)).trans
    (approxMomentEnvelope_mono N hkr hM)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hterm q) heta).trans
    (hbudget.trans (by norm_num))

theorem approxMomentBudget_of_small (N r q : ℕ) {M eta : ℝ} (hM : 0 ≤ M)
    (hsmall : eta ≤ (1 / 2) * (approxMomentEnvelope N r M ^ q)⁻¹) :
    eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2 := by
  have hp : 0 < approxMomentEnvelope N r M := lt_of_lt_of_le zero_lt_one (approxMomentEnvelope_one_le N r hM)
  have h := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hp.le q)
  simpa only [mul_assoc, inv_mul_cancel₀ (pow_pos hp q).ne', mul_one] using h

end Erdos3

end

end OAI
