import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

def approxMomentEnvelope (N r : ℕ) (M : ℝ) : ℝ :=
  (2 : ℝ) ^ (r + 1) * (2 + (N : ℝ)) ^ r * (2 + M)

theorem approxMomentEnvelope_one_le (N r : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    1 ≤ approxMomentEnvelope N r M := by
  unfold approxMomentEnvelope
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith))
  · linarith

theorem approxMomentEnvelope_mono (N : ℕ) {s r : ℕ} (hsr : s ≤ r) {M : ℝ} (hM : 0 ≤ M) :
    approxMomentEnvelope N s M ≤ approxMomentEnvelope N r M := by
  unfold approxMomentEnvelope
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hsr 1))
    (pow_le_pow_right₀ (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) hsr) (by positivity) (by positivity)

theorem approxMomentEnvelope_bounds_term (N k : ℕ) {M eta : ℝ} (hM : 0 ≤ M) (heta : eta ≤ 1) :
    (2 : ℝ) ^ k * (N : ℝ) ^ k * M * (1 + eta) ≤ approxMomentEnvelope N k M := by
  calc
    _ ≤ (2 : ℝ) ^ k * (N : ℝ) ^ k * M * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ (2 : ℝ) ^ k * (2 + (N : ℝ)) ^ k * (2 + M) * 2 := by gcongr <;> linarith
    _ = approxMomentEnvelope N k M := by unfold approxMomentEnvelope; rw [pow_succ]; ring

end Erdos3

end

end OAI
