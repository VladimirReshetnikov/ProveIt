import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# JSWW 1976, Lemmas 2.7, 2.8 and the inequality (iv) of Lemma 2.10

> **Lemma 2.7.** If `q ≥ 1` is an integer and `0 ≤ α < 1/q`, then `1 - qα ≤ (1-α)^q`.
> **Lemma 2.8.** If `0 ≤ α ≤ 1/2`, then `(1-α)⁻¹ ≤ 1 + 2α`.
> **(iv)** (in the proof of Lemma 2.10) `(n+1)^k / C(n,k) ≤ k! + 1` when `(2k)^k ≤ n`,
> derived here in the sharper multiplicative form `k! (n+1)^k < (k!+1) n(n-1)⋯(n-k+1)`.
-/

namespace JSWW1976

open Finset

/-- Lemma 2.7 (Bernoulli's inequality); Mathlib's `one_add_mul_le_pow` with `a = -α`.
The hypothesis `α < 1/q` of the article is not needed. -/
theorem lemma_2_7 {α : ℝ} (hα : α ≤ 1) (q : ℕ) : 1 - q * α ≤ (1 - α) ^ q := by
  have := one_add_mul_le_pow (a := -α) (by linarith) q
  simpa [sub_eq_add_neg, mul_neg] using this

/-- Lemma 2.8: `(1-α)⁻¹ ≤ 1 + 2α` for `0 ≤ α ≤ 1/2`. -/
theorem lemma_2_8 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) : (1 - α)⁻¹ ≤ 1 + 2 * α := by
  have hpos : 0 < 1 - α := by linarith
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith

/-- `2 k² · k! ≤ (2k)^k` for `k ≥ 1`. -/
theorem two_k_sq_factorial_le {k : ℕ} (hk : 1 ≤ k) : 2 * k ^ 2 * k.factorial ≤ (2 * k) ^ k := by
  -- k! ≤ k^(k-1) and 2k ≤ 2^k
  have h1 : k.factorial ≤ k ^ (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    induction m with
    | zero => simp
    | succ m ih =>
      have ih' := ih (by omega)
      calc (m + 1 + 1).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ _
        _ ≤ (m + 2) * (m + 1) ^ m := Nat.mul_le_mul_left _ ih'
        _ ≤ (m + 2) * (m + 2) ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ = (m + 2) ^ (m + 1) := by ring
  have h2 : 2 * k ≤ 2 ^ k := by
    have h := Nat.lt_two_pow_self (n := k - 1)
    calc 2 * k ≤ 2 * 2 ^ (k - 1) := by omega
      _ = 2 ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]
  calc 2 * k ^ 2 * k.factorial ≤ 2 * k ^ 2 * k ^ (k - 1) := Nat.mul_le_mul_left _ h1
    _ = 2 * k * k ^ k := by
      have : k ^ 2 * k ^ (k - 1) = k * k ^ k := by
        rw [show k ^ k = k ^ (k - 1 + 1) by rw [Nat.sub_add_cancel hk], pow_succ]; ring
      rw [mul_assoc, this]; ring
    _ ≤ 2 ^ k * k ^ k := Nat.mul_le_mul_right _ h2
    _ = (2 * k) ^ k := by rw [mul_pow]

/-- The inequality (iv) of Lemma 2.10 in multiplicative form:
`k! (n+1)^k < (k!+1) · n(n-1)⋯(n-k+1)` whenever `1 ≤ k` and `(2k)^k ≤ n`. -/
theorem lemma_2_10_iv {k n : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ k ≤ n) :
    k.factorial * (n + 1) ^ k < (k.factorial + 1) * n.descFactorial k := by
  -- work in ℝ
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : 2 * k ^ 2 ≤ n := by
    have : 2 * k ^ 2 ≤ (2 * k) ^ k := by
      have h := two_k_sq_factorial_le hk
      calc 2 * k ^ 2 = 2 * k ^ 2 * 1 := by ring
        _ ≤ 2 * k ^ 2 * k.factorial := Nat.mul_le_mul_left _ (Nat.factorial_pos k)
        _ ≤ (2 * k) ^ k := h
    exact le_trans this hn
  have hkn' : (2 : ℝ) * k ^ 2 ≤ n := by exact_mod_cast hkn
  have hn0 : (0 : ℝ) < n := by
    have : 2 ≤ n := le_trans (by nlinarith) hkn
    exact_mod_cast (by omega : 0 < n)
  have hkltn : (k : ℝ) < n := by nlinarith
  -- n(n-1)⋯(n-k+1) ≥ (n+1-k)^k
  have hdesc : ((n + 1 - k : ℕ) : ℝ) ^ k ≤ (n.descFactorial k : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    rw [show ((n + 1 - k : ℕ) : ℝ) ^ k = ∏ _i ∈ range k, ((n + 1 - k : ℕ) : ℝ) by simp]
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i hi
      simp only [Finset.mem_range] at hi
      have hkn2 : k ≤ n := by exact_mod_cast hkltn.le
      have hi' : i + 1 ≤ k := hi
      rw [Nat.cast_sub (by omega : k ≤ n + 1), Nat.cast_sub (by omega : i ≤ n)]
      push_cast
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi'
      linarith
  set α : ℝ := k / (n + 1) with hα
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hkα : k * α ≤ 1 / 2 := by
    rw [hα, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  -- (n+1-k)/(n+1) = 1 - α, and Bernoulli gives (1-α)^k ≥ 1 - kα
  have hsub : ((n + 1 - k : ℕ) : ℝ) = (n + 1) * (1 - α) := by
    have : k ≤ n + 1 := by have : (k : ℝ) ≤ n := hkltn.le; exact_mod_cast (by linarith : (k : ℝ) ≤ n + 1)
    rw [Nat.cast_sub this, hα]; push_cast; field_simp
  have hbern : 1 - k * α ≤ (1 - α) ^ k := lemma_2_7 hα1.le k
  have hpos : 0 < 1 - k * α := by linarith
  -- key real inequality: (n+1)^k * k! < (k!+1) (n+1)^k (1-α)^k
  have hβ : (1 - k * α)⁻¹ ≤ 1 + 2 * (k * α) := lemma_2_8 (by positivity) hkα
  have h2kα : 2 * (k * α) < (k.factorial : ℝ)⁻¹ := by
    -- 2 k² /(n+1) < 1/k!  ⟸  2 k² k! ≤ (2k)^k ≤ n < n+1
    have hf : (2 * k ^ 2 * k.factorial : ℝ) ≤ n := by
      have := two_k_sq_factorial_le hk
      exact_mod_cast le_trans this hn
    have hfpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [hα, show 2 * ((k : ℝ) * (k / (n + 1))) = 2 * k ^ 2 / (n + 1) by ring,
      div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ hfpos]
    linarith
  have hfpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  -- (1-α)^(-k) ≤ (1 - kα)⁻¹ ≤ 1 + 2kα < 1 + 1/k!
  have hmain : (k.factorial : ℝ) < (k.factorial + 1) * (1 - α) ^ k := by
    have h1 : (1 - α) ^ k * (1 - k * α)⁻¹ ≥ 1 := by
      rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]; exact hbern
    have h2 : (1 - k * α)⁻¹ < 1 + (k.factorial : ℝ)⁻¹ := by linarith
    have h3 : (1 - α) ^ k * (1 + (k.factorial : ℝ)⁻¹) > 1 := by
      have hp : 0 < (1 - α) ^ k := by positivity
      calc (1 - α) ^ k * (1 + (k.factorial : ℝ)⁻¹) > (1 - α) ^ k * (1 - k * α)⁻¹ := by gcongr
        _ ≥ 1 := h1
    have : (k.factorial : ℝ) * ((1 - α) ^ k * (1 + (k.factorial : ℝ)⁻¹)) > k.factorial * 1 := by
      gcongr
    calc (k.factorial : ℝ) = k.factorial * 1 := by ring
      _ < k.factorial * ((1 - α) ^ k * (1 + (k.factorial : ℝ)⁻¹)) := this
      _ = (k.factorial + 1) * (1 - α) ^ k := by field_simp
  -- assemble: k! (n+1)^k < (k!+1)(n+1)^k (1-α)^k = (k!+1)(n+1-k)^k ≤ (k!+1) descFactorial
  have hfinal : (k.factorial : ℝ) * (n + 1) ^ k < (k.factorial + 1) * (n.descFactorial k : ℝ) := by
    have hp : (0 : ℝ) < (n + 1) ^ k := by positivity
    calc (k.factorial : ℝ) * (n + 1) ^ k < (k.factorial + 1) * (1 - α) ^ k * (n + 1) ^ k := by
          nlinarith
      _ = (k.factorial + 1) * ((n + 1) * (1 - α)) ^ k := by rw [mul_pow]; ring
      _ = (k.factorial + 1) * ((n + 1 - k : ℕ) : ℝ) ^ k := by rw [hsub]
      _ ≤ (k.factorial + 1) * (n.descFactorial k : ℝ) := by gcongr
  exact_mod_cast hfinal

end JSWW1976
