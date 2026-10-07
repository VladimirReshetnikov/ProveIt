import OAI.Combinatorics.Progressions.Sampling.LocalWeightedSampling

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem correlation_self_le_sq (L : Finset G) (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (t : G) : correlation L f f t ≤ M ^ 2 := by
  have hM : 0 ≤ M := (hf 0).1.trans (hf 0).2
  have hcard : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  unfold correlation
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ ∑ x : G, if x ∈ L then M ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ L
      · simp only [hx, ite_true]
        simpa only [pow_two] using mul_le_mul (hf (x + t)).2 (hf x).2 (hf x).1 hM
      · simp [hx, hsupport x hx]
    _ = _ := by simp [mul_comm]

theorem abs_correlation_self_pow_le (L : Finset G) (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (t : G) (q : ℕ) :
    |correlation L f f t ^ q| ≤ M ^ (2 * q) := by
  have hcorr := correlation_nonneg L f f (fun x => (hf x).1) (fun x => (hf x).1) t
  rw [abs_of_nonneg (pow_nonneg hcorr q), pow_mul]
  exact pow_le_pow_left₀ hcorr (correlation_self_le_sq L hL f hsupport hf t) q

end Erdos3.LocalConvolution

end

end OAI
