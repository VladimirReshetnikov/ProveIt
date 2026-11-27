import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Passing to a limit after excluding a squarefree prime

At a prime of degree `d`, the old count splits into the new count and an earlier
new count shifted by `d`. After normalization the latter has weight `q⁻ᵈ < 1`.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology

/-- Removing one prime divides the limiting normalized count by `1 + c`.
The bound is uniform over all residue classes of the degree modulo `d`. -/
theorem tendsto_of_prime_exclusion_recurrence (a b : ℕ → ℝ) (d : ℕ) (c A : ℝ)
    (_hd : 0 < d) (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (hbound : ∀ n, b n ∈ Set.Icc 0 1) (ha : Tendsto a atTop (𝓝 A))
    (hrec : ∀ n ≥ d, a n = b n + c * b (n-d)) :
    Tendsto b atTop (𝓝 (A * (1+c)⁻¹)) := by
  let v := A * (1+c)⁻¹
  have hv : A = v + c*v := by
    dsimp [v]
    field_simp [show 1 + c ≠ 0 by linarith]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hclose := Metric.tendsto_nhds.mp ha (ε/2*(1-c)) (mul_pos (by positivity) (by linarith))
  let M := 1 + |v|
  have hM : 0 < M := by dsimp [M]; positivity
  have hiter (k : ℕ) : ∀ᶠ n in atTop, |b n-v| ≤ ε/2 + c^k*M := by
    induction k with
    | zero =>
      apply Eventually.of_forall
      intro n
      have h := abs_sub (b n) v
      rw [abs_of_nonneg (hbound n).1] at h
      simp only [pow_zero, one_mul]
      dsimp [M]
      linarith [(hbound n).2]
    | succ k ih =>
      filter_upwards [hclose, (tendsto_sub_atTop_nat d).eventually ih, eventually_ge_atTop d]
        with n hnear hprev hnd
      rw [Real.dist_eq] at hnear
      have he : b n-v = (a n-A) - c*(b (n-d)-v) := by
        rw [hrec n hnd]
        linear_combination hv
      calc
        |b n-v| = |(a n-A) - c*(b (n-d)-v)| := congrArg abs he
        _ ≤ |a n-A| + |c*(b (n-d)-v)| := abs_sub _ _
        _ ≤ ε/2*(1-c) + c*(ε/2 + c^k*M) := by
          rw [abs_mul, abs_of_nonneg hc₀]
          exact add_le_add hnear.le (mul_le_mul_of_nonneg_left hprev hc₀)
        _ = ε/2 + c^(k+1)*M := by ring
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (show (0:ℝ) < ε/2 by positivity) hM) hc₁
  filter_upwards [hiter k] with n hn
  rw [Real.dist_eq]
  change |b n-v| < ε
  linarith [(lt_div_iff₀ hM).mp hk]

end GRHArticle.ProgressionFree
