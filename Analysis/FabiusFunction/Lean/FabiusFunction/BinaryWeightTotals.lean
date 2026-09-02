import FabiusFunction.DyadicClosedForm
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Totals of the binary weight: `∑_{n<N} w(n)`

The binary weight `w(n) = binaryWeight n` is the exponent of the
Thue–Morse sign `ε(n) = (-1)^(w n)`; its running total
`S(N) = ∑_{n<N} w(n)` is the classical object of Bellman–Shapiro and
Trollope–Delange: `S(N) = ½·N·log₂N + N·F(log₂N)` with `F` bounded,
continuous, and nowhere differentiable.  This module proves the exact
dyadic values and the two-sided `O(N)` error bound with explicit
constant, by the top-digit decomposition `N = 2^L + r`, `r < 2^L`,
`L = ⌊log₂N⌋`:

`S(2^L + r) = S(2^L) + r + S(r)`,

since every `n < 2^L` gains exactly one bit under `n ↦ 2^L + n`.

* `binaryWeightTotal` — `S(N)`.
* `binaryWeightTotal_two_mul` — the doubling recursion
  `S(2M) = 2·S(M) + M`.
* `two_mul_binaryWeightTotal_two_pow` — **the exact dyadic value**
  `S(2^L) = L·2^(L-1)`, stated as `2·S(2^L) = L·2^L`.
* `binaryWeightTotal_two_pow_add` — the top-digit decomposition.
* `two_mul_binaryWeightTotal_le` — `2·S(N) ≤ N·(⌊log₂N⌋ + 1)`.
* `le_two_mul_binaryWeightTotal_add` — `N·⌊log₂N⌋ ≤ 2·S(N) + N`.
* `abs_binaryWeightTotal_sub_le` — **the Trollope–Delange error bound**
  `|S(N) - ½·N·log₂N| ≤ N` for every `N`.  (Numerically the ratio
  `|S(N) - ½N log₂N|/N` never exceeds `0.208` below `2^18`; Delange's
  exact range for `F` is `[-0.1458…, 0]`.)
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The running total of the binary weight, `S(N) = ∑_{n<N} w(n)`. -/
def binaryWeightTotal (N : ℕ) : ℕ :=
  ∑ n ∈ range N, binaryWeight n

@[simp] theorem binaryWeightTotal_zero : binaryWeightTotal 0 = 0 := by
  simp [binaryWeightTotal]

/-- **The doubling recursion** `S(2M) = 2·S(M) + M`: the even and odd
halves carry the same weights, the odd half one more bit each. -/
theorem binaryWeightTotal_two_mul (M : ℕ) :
    binaryWeightTotal (2 * M) = 2 * binaryWeightTotal M + M := by
  unfold binaryWeightTotal
  rw [sum_range_two_mul]
  simp only [binaryWeight_two_mul, binaryWeight_two_mul_add_one]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    card_range, smul_eq_mul, mul_one]
  ring

/-- **The exact dyadic value** `S(2^L) = L·2^(L-1)`, written without
natural subtraction as `2·S(2^L) = L·2^L`. -/
theorem two_mul_binaryWeightTotal_two_pow (L : ℕ) :
    2 * binaryWeightTotal (2 ^ L) = L * 2 ^ L := by
  induction L with
  | zero => simp [binaryWeightTotal, binaryWeight]
  | succ L ih =>
      rw [pow_succ, mul_comm (2 ^ L) 2, binaryWeightTotal_two_mul]
      calc 2 * (2 * binaryWeightTotal (2 ^ L) + 2 ^ L)
          = 2 * (2 * binaryWeightTotal (2 ^ L)) + 2 * 2 ^ L := by ring
        _ = 2 * (L * 2 ^ L) + 2 * 2 ^ L := by rw [ih]
        _ = (L + 1) * (2 * 2 ^ L) := by ring

/-- **The top-digit decomposition**: for `r < 2^L`,
`S(2^L + r) = S(2^L) + r + S(r)`. -/
theorem binaryWeightTotal_two_pow_add (L r : ℕ) (hr : r < 2 ^ L) :
    binaryWeightTotal (2 ^ L + r) =
      binaryWeightTotal (2 ^ L) + r + binaryWeightTotal r := by
  unfold binaryWeightTotal
  rw [Finset.sum_range_add]
  have h : ∀ n ∈ range r, binaryWeight (2 ^ L + n) = binaryWeight n + 1 :=
    fun n hn =>
      binaryWeight_add_pow_two L n (lt_of_lt_of_le (mem_range.1 hn) hr.le)
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const,
    card_range, smul_eq_mul, mul_one]
  ring

/-- The top digit of a positive `N`: `N = 2^L + r` with `L = ⌊log₂N⌋`
and `r < 2^L`. -/
theorem exists_top_digit (N : ℕ) (hN : 0 < N) :
    ∃ r, N = 2 ^ Nat.log 2 N + r ∧ r < 2 ^ Nat.log 2 N := by
  have hlow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hhigh : N < 2 ^ (Nat.log 2 N + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two N
  rw [pow_succ] at hhigh
  exact ⟨N - 2 ^ Nat.log 2 N, by omega, by omega⟩

/-- **The upper bound** `2·S(N) ≤ N·(⌊log₂N⌋ + 1)`: each of the
`⌊log₂N⌋ + 1` bit positions is set in at most half of `[0, N)`. -/
theorem two_mul_binaryWeightTotal_le (N : ℕ) :
    2 * binaryWeightTotal N ≤ N * (Nat.log 2 N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · obtain ⟨r, hr, hrlt⟩ := exists_top_digit N hN
      set L := Nat.log 2 N with hL
      have h2L : 0 < 2 ^ L := by positivity
      have hrN : r < N := by omega
      have hsplit := binaryWeightTotal_two_pow_add L r hrlt
      have hpow := two_mul_binaryWeightTotal_two_pow L
      have hSr : 2 * binaryWeightTotal r ≤ r * L := by
        rcases Nat.eq_zero_or_pos r with rfl | hr0
        · simp
        · have hlog : Nat.log 2 r < L := Nat.log_lt_of_lt_pow hr0.ne' hrlt
          calc 2 * binaryWeightTotal r ≤ r * (Nat.log 2 r + 1) := ih r hrN
            _ ≤ r * L := Nat.mul_le_mul_left r (by omega)
      rw [hr, hsplit]
      nlinarith [hpow, hSr, hrlt]

/-- **The lower bound** `N·⌊log₂N⌋ ≤ 2·S(N) + N`. -/
theorem le_two_mul_binaryWeightTotal_add (N : ℕ) :
    N * Nat.log 2 N ≤ 2 * binaryWeightTotal N + N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · obtain ⟨r, hr, hrlt⟩ := exists_top_digit N hN
      set L := Nat.log 2 N with hL
      have h2L : 0 < 2 ^ L := by positivity
      have hrN : r < N := by omega
      have hsplit := binaryWeightTotal_two_pow_add L r hrlt
      have hpow := two_mul_binaryWeightTotal_two_pow L
      -- the recursive contribution: `r·L ≤ 2·S(r) + r + 2^L`
      have hSr : r * L ≤ 2 * binaryWeightTotal r + r + 2 ^ L := by
        rcases Nat.eq_zero_or_pos r with rfl | hr0
        · simp
        · have hIH := ih r hrN
          have hlog : Nat.log 2 r < L := Nat.log_lt_of_lt_pow hr0.ne' hrlt
          have hr' : r < 2 ^ (Nat.log 2 r + 1) :=
            Nat.lt_pow_succ_log_self one_lt_two r
          obtain ⟨e, he⟩ : ∃ e, L = Nat.log 2 r + 1 + e :=
            ⟨L - (Nat.log 2 r + 1), by omega⟩
          have hgap : r * (e + 1) ≤ 2 ^ L := by
            calc r * (e + 1) ≤ 2 ^ (Nat.log 2 r + 1) * (e + 1) :=
                  Nat.mul_le_mul_right _ hr'.le
              _ ≤ 2 ^ (Nat.log 2 r + 1) * 2 ^ e := by
                  refine Nat.mul_le_mul_left _ ?_
                  have := Nat.lt_two_pow_self (n := e)
                  omega
              _ = 2 ^ L := by rw [← pow_add, he]
          calc r * L = r * Nat.log 2 r + r * (e + 1) := by rw [he]; ring
            _ ≤ (2 * binaryWeightTotal r + r) + 2 ^ L :=
                Nat.add_le_add hIH hgap
      rw [hr, hsplit]
      nlinarith [hpow, hSr, hrlt]

/-- `⌊log₂N⌋ ≤ log₂N < ⌊log₂N⌋ + 1` for `N ≥ 1`, in `ℝ`. -/
theorem natLog_le_logb (N : ℕ) (hN : 0 < N) :
    (Nat.log 2 N : ℝ) ≤ Real.logb 2 N ∧
      Real.logb 2 N ≤ (Nat.log 2 N : ℝ) + 1 := by
  have hlow : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hhigh : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self one_lt_two N).le
  have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one one_lt_two
  constructor
  · calc (Nat.log 2 N : ℝ) = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 N) := by
          rw [Real.logb_pow, hself, mul_one]
      _ ≤ Real.logb 2 N := Real.logb_le_logb_of_le one_lt_two (by positivity) hlow
  · calc Real.logb 2 N ≤ Real.logb 2 ((2 : ℝ) ^ (Nat.log 2 N + 1)) :=
          Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hN) hhigh
      _ = (Nat.log 2 N : ℝ) + 1 := by
          rw [Real.logb_pow, hself, mul_one]
          push_cast
          ring

/-- **The Trollope–Delange error bound with constant one**:
`|S(N) - ½·N·log₂N| ≤ N` for every `N`. -/
theorem abs_binaryWeightTotal_sub_le (N : ℕ) :
    |(binaryWeightTotal N : ℝ) - (N : ℝ) * Real.logb 2 N / 2| ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hup : (2 : ℝ) * binaryWeightTotal N ≤ N * (Nat.log 2 N + 1) := by
      exact_mod_cast two_mul_binaryWeightTotal_le N
    have hlo : (N : ℝ) * Nat.log 2 N ≤ 2 * binaryWeightTotal N + N := by
      exact_mod_cast le_two_mul_binaryWeightTotal_add N
    obtain ⟨hL1, hL2⟩ := natLog_le_logb N hN
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_le]
    constructor <;> nlinarith [hup, hlo, hL1, hL2, hN0]

end Fabius
