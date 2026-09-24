import Mathlib.Tactic

/-!
# Reading a three-digit window of a signed coefficient sum

Section 5 of `Papers/1980/AFFINE_RADIX_95_PROOF.md`: the low base-`B` digits
of the positive integer `σ` are those of a signed coefficient sum
`Σ aⱼ Bʲ`.  At a target position `t` the layout supplies zero coefficients at
`t − 5, t − 4, t − 2, t − 1`, a reset coefficient `x² ∈ [1, B² − 1]` at
`t − 3`, and zero coefficients at `t + 1, t + 2`.  Everything below `t − 5`
is small (`32 · |Low| ≤ B^(t−3)`).  Then the carry into position `t` is
zero, and the three digits at `t, t + 1, t + 2` are the residue of the
target coefficient `G = a_t` modulo `B³`.

This file isolates that arithmetic from the summation bookkeeping: the
decomposition `σ = Low + x² B^(t−3) + G B^t + B^(t+3) High` is a hypothesis.
`window_digits` gives `(σ / B^t) % B³ = (G mod B³)`; `window_nonneg_of_small`
shows that a window whose three digits are all `≤ 3` has `G ≥ 0` when
`64 |G| < B³`.
-/

namespace Jones1980

/-- The carry into the window is zero and the window shows `G` modulo `B³`. -/
theorem window_digits {B t : ℕ} (hB : 64 ≤ B) (ht : 4 ≤ t) {σ : ℕ} {Low x2 G High : ℤ}
    (hσ : (σ : ℤ) = Low + x2 * (B : ℤ) ^ (t - 3) + G * (B : ℤ) ^ t + (B : ℤ) ^ (t + 3) * High)
    (hLow : 32 * |Low| ≤ (B : ℤ) ^ (t - 3)) (hx1 : 1 ≤ x2) (hx2 : x2 + 1 ≤ (B : ℤ) ^ 2) :
    ((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3 = G % (B : ℤ) ^ 3 := by
  have hBZ : (64 : ℤ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℤ) < B := by linarith
  -- `B^(t-3) = B * B^(t-4)`, `B^(t-1) = B^2 * B^(t-3)`, `B^t = B * B^(t-1)`
  have e3 : (B : ℤ) ^ (t - 3) = B * B ^ (t - 4) := by
    rw [← pow_succ']; congr 1; omega
  have e1 : (B : ℤ) ^ (t - 1) = B ^ 2 * B ^ (t - 3) := by
    rw [← pow_add]; congr 1; omega
  have et : (B : ℤ) ^ t = B * B ^ (t - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp4 : (0 : ℤ) < B ^ (t - 4) := by positivity
  have hp3 : (0 : ℤ) < B ^ (t - 3) := by positivity
  -- the middle part `M = Low + x2 B^(t-3)` satisfies `0 ≤ M < B^t`
  set M := Low + x2 * (B : ℤ) ^ (t - 3) with hM
  have habs := abs_le.1 (show |Low| ≤ (B : ℤ) ^ (t - 3) by linarith [abs_nonneg Low])
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (B : ℤ) ^ (t - 3) ≤ x2 * (B : ℤ) ^ (t - 3) := le_mul_of_one_le_left hp3.le hx1
    linarith
  have hMt : M < (B : ℤ) ^ t := by
    rw [hM, et, e1]
    have h1 : x2 * (B : ℤ) ^ (t - 3) ≤ (B ^ 2 - 1) * B ^ (t - 3) :=
      mul_le_mul_of_nonneg_right (by linarith) hp3.le
    have h2 : (0 : ℤ) < B ^ 2 * B ^ (t - 3) := by positivity
    nlinarith
  -- `σ = M + B^t W` with `W = G + B^3 High ≥ 0`
  set W := G + (B : ℤ) ^ 3 * High with hW
  have hσW : (σ : ℤ) = M + (B : ℤ) ^ t * W := by
    rw [hσ, hM, hW, pow_add]; ring
  have hW0 : 0 ≤ W := by
    by_contra hneg; push Not at hneg
    have : (B : ℤ) ^ t * W ≤ (B : ℤ) ^ t * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    have hσ0 : (0 : ℤ) ≤ σ := by exact_mod_cast Nat.zero_le σ
    linarith
  -- integer division
  have hdiv : ((σ / B ^ t : ℕ) : ℤ) = W := by
    have hBt : (0 : ℤ) < (B : ℤ) ^ t := by positivity
    have hpos : 0 < B ^ t := by positivity
    rw [Int.natCast_div, Nat.cast_pow, hσW]
    rw [Int.add_mul_ediv_left M W hBt.ne', Int.ediv_eq_zero_of_lt hM0 hMt]
    ring
  rw [hdiv, hW, Int.add_mul_emod_self_left]

/-- If `64 |G| < B³` and the residue `G mod B³` has all three base-`B` digits `≤ 3`,
then `G ≥ 0` and `G = d₀ + d₁ B + d₂ B²` with the digits `dᵢ ≤ 3`. -/
theorem window_nonneg_of_small {B : ℕ} (hB : 64 ≤ B) {G : ℤ} (hG : 64 * |G| < (B : ℤ) ^ 3)
    (hd0 : (G % (B : ℤ) ^ 3) % B ≤ 3) (hd1 : (G % (B : ℤ) ^ 3) / B % B ≤ 3)
    (hd2 : (G % (B : ℤ) ^ 3) / B / B ≤ 3) :
    0 ≤ G ∧ G = (G % (B : ℤ) ^ 3) % B + (G % (B : ℤ) ^ 3) / B % B * B +
      (G % (B : ℤ) ^ 3) / B / B * B ^ 2 := by
  have hBZ : (64 : ℤ) ≤ B := by exact_mod_cast hB
  have hB3 : (0 : ℤ) < (B : ℤ) ^ 3 := by positivity
  have hB2 : (0 : ℤ) < (B : ℤ) ^ 2 := by positivity
  have hB0 : (0 : ℤ) < B := by linarith
  set N := G % (B : ℤ) ^ 3 with hN
  have hN0 : 0 ≤ N := Int.emod_nonneg _ hB3.ne'
  have hNlt : N < (B : ℤ) ^ 3 := Int.emod_lt_of_pos _ hB3
  -- the three digits reconstruct `N`
  have hdigits : N = N % B + N / B % B * B + N / B / B * B ^ 2 := by
    have h1 := Int.emod_def N B
    have h2 := Int.emod_def (N / B) B
    linear_combination (-1 : ℤ) * h1 + (-(B : ℤ)) * h2
  -- a negative `G` would have a top digit above 3
  have hGnn : 0 ≤ G := by
    by_contra hneg; push Not at hneg
    have habs : |G| = -G := abs_of_neg hneg
    rw [habs] at hG
    -- `N = G + B^3`, which exceeds `63 B^3 / 64 ≥ 4 B^2`
    have hNeq : N = G + (B : ℤ) ^ 3 := by
      rw [hN]
      have h1 : (G + (B : ℤ) ^ 3 * 1) % (B : ℤ) ^ 3 = G % (B : ℤ) ^ 3 :=
        Int.add_mul_emod_self_left G ((B : ℤ) ^ 3) 1
      rw [mul_one] at h1
      rw [← h1]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    have h4 : 4 * (B : ℤ) ^ 2 ≤ N := by
      rw [hNeq]
      have : 256 * (B : ℤ) ^ 2 ≤ 63 * (B : ℤ) ^ 3 := by
        have : (B : ℤ) ^ 3 = B ^ 2 * B := by ring
        rw [this]; nlinarith
      linarith
    have h5 : 4 * (B : ℤ) ≤ N / B := (Int.le_ediv_iff_mul_le hB0).2 (by nlinarith)
    have : 4 ≤ N / B / B := (Int.le_ediv_iff_mul_le hB0).2 h5
    omega
  refine ⟨hGnn, ?_⟩
  have : N = G := by
    rw [hN]
    have habs : |G| = G := abs_of_nonneg hGnn
    rw [habs] at hG
    exact Int.emod_eq_of_lt hGnn (by linarith)
  rw [← this]; exact hdigits

end Jones1980
