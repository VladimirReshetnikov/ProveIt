import IntegerPoints.ExponentialSums

/-!
# The trivial exponent pair

`(0, 1)` is an exponent pair: the trivial bound `|∑_{a<n≤b} e(f(n))| ≤ b - a + 1 ≤ 3N`.
This shows that `IsExponentPair` is satisfiable.
-/

open Finset Real

namespace LeanProofs.IntegerPoints

/-- `|e(t)| = 1`. -/
theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * t).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- The number of integers in `(a, b] ⊆ [N, 2N]` is at most `3N`. -/
theorem card_intRange_le {N a b : ℝ} (hN : 0 < N) (ha : N ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * N) :
    ((intRange a b).card : ℝ) ≤ 3 * N := by
  rw [intRange, Nat.card_Ioc]
  rcases lt_or_ge b 1 with h | h
  · have : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.2 h
    rw [this, Nat.zero_sub, Nat.cast_zero]
    positivity
  · have h1 : (⌊b⌋₊ : ℝ) ≤ 2 * N := le_trans (Nat.floor_le (by linarith)) hb
    have h2 : ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) ≤ (⌊b⌋₊ : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    have h3 : (1 : ℝ) ≤ b := h
    linarith

/-- The trivial exponent pair `(0, 1)`. -/
theorem isExponentPair_zero_one : IsExponentPair 0 1 := by
  refine ⟨le_rfl, by norm_num, by norm_num, le_rfl, fun s hs => ⟨1, 1 / 4, 3, by norm_num,
    by norm_num, fun N y a b f hN hy hf => ?_⟩⟩
  obtain ⟨hNa, hab, hb2N, -, -⟩ := hf
  rw [Real.rpow_zero, one_mul, Real.rpow_one]
  have h0 : 0 ≤ y⁻¹ * N ^ s := by positivity
  calc ‖∑ n ∈ intRange a b, e (f n)‖ ≤ ∑ n ∈ intRange a b, ‖e (f n)‖ := norm_sum_le _ _
    _ = (intRange a b).card := by simp [norm_e]
    _ ≤ 3 * N := card_intRange_le hN hNa hab hb2N
    _ ≤ 3 * (N + y⁻¹ * N ^ s) := by linarith

end LeanProofs.IntegerPoints
