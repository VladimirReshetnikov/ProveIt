import Diophantine.Paper1980.Windows93

/-!
# The tested window of the 90-operation layout

`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, Section 5.  A tested start `r` is
preceded by the empty positions `r − 6, r − 5`, the reset position `r − 4`
(raw value `x² + …`, positive and below `B³`), the empty positions
`r − 3, r − 2`, and the position `r − 1` (empty, or the padding value `y ≥ 0`
of the last unit row); the three digits at `r, r + 1, r + 2` are then the
residue of `G + ⌊y / B⌋` modulo `B³`, where `G` is the raw value at `r`.  The
digit reading `window_nonneg_of_small` of `Window93.lean` is shared.
-/

namespace Jones1980

/-- The window with the reset four positions below the start. -/
theorem window_digits_pad90 {B t : ℕ} (hB : 64 ≤ B) (ht : 4 ≤ t) {σ : ℕ} {Low x2 y G High : ℤ}
    (hσ : (σ : ℤ) = Low + x2 * (B : ℤ) ^ (t - 4) + y * (B : ℤ) ^ (t - 1) + G * (B : ℤ) ^ t +
      (B : ℤ) ^ (t + 3) * High)
    (hLow : 32 * |Low| ≤ (B : ℤ) ^ (t - 4)) (hx1 : 1 ≤ x2) (hx2 : x2 + 1 ≤ (B : ℤ) ^ 3)
    (hy : 0 ≤ y) :
    ((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3 = (G + y / B) % (B : ℤ) ^ 3 := by
  have hBZ : (64 : ℤ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℤ) < B := by linarith
  have e1 : (B : ℤ) ^ (t - 1) = B ^ 3 * B ^ (t - 4) := by
    rw [← pow_add]; congr 1; omega
  have et : (B : ℤ) ^ t = B * B ^ (t - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp4 : (0 : ℤ) < B ^ (t - 4) := by positivity
  have hp1 : (0 : ℤ) < B ^ (t - 1) := by positivity
  -- split `y` into its carry and its digit
  have hydiv := Int.emod_def y B
  have hy0 : 0 ≤ y % B := Int.emod_nonneg _ hB0.ne'
  have hyB : y % B < B := Int.emod_lt_of_pos _ hB0
  -- the low part `M = Low + x2 B^(t-4) + (y % B) B^(t-1)` satisfies `0 ≤ M < B^t`
  set M := Low + x2 * (B : ℤ) ^ (t - 4) + (y % B) * (B : ℤ) ^ (t - 1) with hM
  have habs : -(B : ℤ) ^ (t - 4) < Low ∧ Low < (B : ℤ) ^ (t - 4) :=
    abs_lt.1 (show |Low| < (B : ℤ) ^ (t - 4) by linarith [abs_nonneg Low])
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (B : ℤ) ^ (t - 4) ≤ x2 * (B : ℤ) ^ (t - 4) := le_mul_of_one_le_left hp4.le hx1
    have : 0 ≤ (y % B) * (B : ℤ) ^ (t - 1) := by positivity
    linarith
  have hMt : M < (B : ℤ) ^ t := by
    rw [hM, et, e1]
    have h1 : x2 * (B : ℤ) ^ (t - 4) ≤ (B ^ 3 - 1) * B ^ (t - 4) :=
      mul_le_mul_of_nonneg_right (by linarith) hp4.le
    have h2 : (y % B) * (B ^ 3 * (B : ℤ) ^ (t - 4)) ≤ (B - 1) * (B ^ 3 * (B : ℤ) ^ (t - 4)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : (0 : ℤ) < B ^ 3 * B ^ (t - 4) := by positivity
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

/-- The binary digit bounds of a window, in the (weaker) form required by
`window_nonneg_of_small`. -/
theorem window_digit_bounds_bin {B t σ : ℕ}
    (h0 : σ / B ^ t % B ≤ 1) (h1 : σ / B ^ (t + 1) % B ≤ 1) (h2 : σ / B ^ (t + 2) % B ≤ 1) :
    (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) % B ≤ 3 ∧
      (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) / B % B ≤ 3 ∧
      (((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3) / B / B ≤ 3 :=
  window_digit_bounds (by omega) (by omega) (by omega)

/-- The value of a binary window: `G = d₀ + d₁ B + d₂ B²` with binary digits `dᵢ`. -/
theorem window_value_bin {B t σ : ℕ} (hB : 64 ≤ B) {G : ℤ} (hG : 64 * |G| < (B : ℤ) ^ 3)
    (hres : ((σ / B ^ t : ℕ) : ℤ) % (B : ℤ) ^ 3 = G % (B : ℤ) ^ 3)
    (h0 : σ / B ^ t % B ≤ 1) (h1 : σ / B ^ (t + 1) % B ≤ 1) (h2 : σ / B ^ (t + 2) % B ≤ 1) :
    0 ≤ G ∧ G = ((σ / B ^ t % B : ℕ) : ℤ) + ((σ / B ^ (t + 1) % B : ℕ) : ℤ) * B +
      ((σ / B ^ (t + 2) % B : ℕ) : ℤ) * B ^ 2 := by
  obtain ⟨b0, b1, b2⟩ := window_digit_bounds_bin h0 h1 h2
  rw [hres] at b0 b1 b2
  obtain ⟨hG0, hGeq⟩ := window_nonneg_of_small hB hG b0 b1 b2
  refine ⟨hG0, ?_⟩
  obtain ⟨c0, c1, c2⟩ := Iso.window_digits_cast B t σ
  rw [hres] at c0 c1 c2
  rw [hGeq, c0, c1, c2]

end Jones1980
