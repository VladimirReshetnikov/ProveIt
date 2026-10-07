import OAI.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem bounded_cutoff_score_lower {X : Type*} [Fintype X]
    (f b : X → ℝ) {M epsilon sigma : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) (hb : (𝔼 x, |1 - b x|) ≤ epsilon)
    (hscore : sigma ≤ 𝔼 x, f x) :
    sigma - M * epsilon ≤ 𝔼 x, f x * b x := by
  have hloss : (𝔼 x, f x * (1 - b x)) ≤ M * epsilon := by
    calc
      _ ≤ 𝔼 x, M * |1 - b x| := by
        apply Finset.expect_le_expect
        intro x _
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _))
      _ = M * (𝔼 x, |1 - b x|) := (Finset.mul_expect ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hM
  have he : (𝔼 x, f x) = (𝔼 x, f x * b x) + (𝔼 x, f x * (1 - b x)) := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro x _
    ring
  linarith

theorem interiorIntervalCutoff_score {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    {M sigma : ℝ} (hM : 0 < M) (hsigma : 0 < sigma)
    (hf : ∀ x, |f x| ≤ M) (hscore : sigma ≤ 𝔼 x, f x)
    (eta : ℝ≥0) (heta : 0 < eta) (hwidth : (eta : ℝ) ≤ sigma / (100 * M))
    (hN : 1 / (N : ℝ) ≤ sigma / (100 * M)) :
    3 * sigma / 4 ≤ 𝔼 x, f x * interiorIntervalCutoff eta ((x.val : ℝ) / N) := by
  have h := bounded_cutoff_score_lower f
    (fun x => interiorIntervalCutoff eta ((x.val : ℝ) / N)) hM.le hf
    (interiorIntervalCutoff_cyclic_loss eta heta) hscore
  have he : M * (sigma / (100 * M)) = sigma / 100 := by field_simp [hM.ne']
  have hw := mul_le_mul_of_nonneg_left hwidth hM.le
  have hrec := mul_le_mul_of_nonneg_left hN hM.le
  have hthree : (3 : ℝ) / N = 3 * (1 / N) := by ring
  rw [he] at hw hrec
  rw [hthree] at h
  nlinarith

end Erdos3

end

end OAI
