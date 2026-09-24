import Diophantine.Paper1980.Window93
import Diophantine.Paper1980.Digits93

/-!
# The three-digit window with a padding carry (Section 5)

`window_digits_pad` generalizes `window_digits`: a nonnegative coefficient
`y` at position `t − 1` (the padding `5x²` or `7x²` of the last two unit
targets, or `0`) contributes the carry `⌊y / B⌋` into the target, so that the
window shows `G + ⌊y / B⌋` modulo `B³`.  `window_digit_bounds` converts the
three digit bounds read from the third mask into the hypotheses of
`window_nonneg_of_small`.
-/

namespace Jones1980

/-- The window with an incoming padding carry: the three digits at `t, t + 1, t + 2` are the
residue of `G + ⌊y / B⌋` modulo `B³`. -/
theorem window_digits_pad {B t : ℕ} (hB : 64 ≤ B) (ht : 4 ≤ t) {σ : ℕ} {Low x2 y G High : ℤ}
    (hσ : (σ : ℤ) = Low + x2 * (B : ℤ) ^ (t - 3) + y * (B : ℤ) ^ (t - 1) + G * (B : ℤ) ^ t +
      (B : ℤ) ^ (t + 3) * High)
    (hLow : 32 * |Low| ≤ (B : ℤ) ^ (t - 3)) (hx1 : 1 ≤ x2) (hx2 : x2 + 1 ≤ (B : ℤ) ^ 2)
    (hy : 0 ≤ y) :
    ((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3 = (G + y / B) % (B : ℤ) ^ 3 := by
  have hBZ : (64 : ℤ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℤ) < B := by linarith
  have e1 : (B : ℤ) ^ (t - 1) = B ^ 2 * B ^ (t - 3) := by
    rw [← pow_add]; congr 1; omega
  have et : (B : ℤ) ^ t = B * B ^ (t - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp3 : (0 : ℤ) < B ^ (t - 3) := by positivity
  have hp1 : (0 : ℤ) < B ^ (t - 1) := by positivity
  -- split `y` into its carry and its digit
  have hydiv := Int.emod_def y B
  have hy0 : 0 ≤ y % B := Int.emod_nonneg _ hB0.ne'
  have hyB : y % B < B := Int.emod_lt_of_pos _ hB0
  -- the low part `M = Low + x2 B^(t-3) + (y % B) B^(t-1)` satisfies `0 ≤ M < B^t`
  set M := Low + x2 * (B : ℤ) ^ (t - 3) + (y % B) * (B : ℤ) ^ (t - 1) with hM
  have habs : -(B : ℤ) ^ (t - 3) < Low ∧ Low < (B : ℤ) ^ (t - 3) :=
    abs_lt.1 (show |Low| < (B : ℤ) ^ (t - 3) by linarith [abs_nonneg Low])
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (B : ℤ) ^ (t - 3) ≤ x2 * (B : ℤ) ^ (t - 3) := le_mul_of_one_le_left hp3.le hx1
    have : 0 ≤ (y % B) * (B : ℤ) ^ (t - 1) := by positivity
    linarith
  have hMt : M < (B : ℤ) ^ t := by
    rw [hM, et, e1]
    have h1 : x2 * (B : ℤ) ^ (t - 3) ≤ (B ^ 2 - 1) * B ^ (t - 3) :=
      mul_le_mul_of_nonneg_right (by linarith) hp3.le
    have h2 : (y % B) * (B ^ 2 * (B : ℤ) ^ (t - 3)) ≤ (B - 1) * (B ^ 2 * (B : ℤ) ^ (t - 3)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : (0 : ℤ) < B ^ 2 * B ^ (t - 3) := by positivity
    nlinarith
  -- `σ = M + B^t W` with `W = G + y / B + B^3 High ≥ 0`
  set W := G + y / B + (B : ℤ) ^ 3 * High with hW
  have hσW : (σ : ℤ) = M + (B : ℤ) ^ t * W := by
    rw [hσ, hM, hW, pow_add]
    have : y * (B : ℤ) ^ (t - 1) = (y % B) * B ^ (t - 1) + (y / B) * B ^ t := by
      rw [et, hydiv]; ring
    linear_combination this
  have hW0 : 0 ≤ W := by
    by_contra hneg; push Not at hneg
    have : (B : ℤ) ^ t * W ≤ (B : ℤ) ^ t * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    have hσ0 : (0 : ℤ) ≤ σ := by exact_mod_cast Nat.zero_le σ
    linarith
  have hdiv : ((σ / B ^ t : ℕ) : ℤ) = W := by
    have hBt : (0 : ℤ) < (B : ℤ) ^ t := by positivity
    rw [Int.natCast_div, Nat.cast_pow, hσW]
    rw [Int.add_mul_ediv_left M W hBt.ne', Int.ediv_eq_zero_of_lt hM0 hMt]
    ring
  rw [hdiv, hW, Int.add_mul_emod_self_left]

/-- The digit bounds of the window, in the form required by `window_nonneg_of_small`. -/
theorem window_digit_bounds {B t σ : ℕ}
    (h0 : σ / B ^ t % B ≤ 3) (h1 : σ / B ^ (t + 1) % B ≤ 3) (h2 : σ / B ^ (t + 2) % B ≤ 3) :
    (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) % B ≤ 3 ∧
      (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) / B % B ≤ 3 ∧
      (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) / B / B ≤ 3 := by
  have hN : ((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3 = ((σ / B ^ t % B ^ 3 : ℕ) : ℤ) := by norm_cast
  rw [hN]
  have e1 : σ / B ^ t / B = σ / B ^ (t + 1) := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have e2 : σ / B ^ t / B ^ 2 = σ / B ^ (t + 2) := by rw [pow_add, Nat.div_div_eq_div_mul]
  refine ⟨?_, ?_, ?_⟩
  · have : (σ / B ^ t % B ^ 3 % B : ℕ) ≤ 3 := by
      rw [Nat.mod_mod_of_dvd _ (dvd_pow_self B (by norm_num))]; exact h0
    exact_mod_cast this
  · have : (σ / B ^ t % B ^ 3 / B % B : ℕ) ≤ 3 := by
      have := Iso.digit_mod_pow (σ / B ^ t) B (show 1 < 3 by norm_num)
      rw [pow_one] at this
      rw [this, e1]; exact h1
    exact_mod_cast this
  · have : (σ / B ^ t % B ^ 3 / B / B : ℕ) ≤ 3 := by
      rw [Iso.digit_mod_pow_three_top, e2]; exact h2
    exact_mod_cast this

end Jones1980
