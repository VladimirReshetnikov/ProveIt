import FabiusFunction.ThueMorseNewman
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Newman's theorem, quantitative form

`ThueMorseNewman` proves the *sign* of Newman's phenomenon: the
multiples of three below `N` with even binary weight outnumber those
with odd binary weight, `N₃(N) = T₀(N) ≥ 1`.  Newman (1969) also gave
the *size*: `N₃(N)` grows like `N^α` with `α = log₄3 = 0.7924…`, his
constants being `1/20 < N₃(N)/N^α < 5`.  This module derives the growth
from the base-four step bracket

`3·T₀(M) - 2 ≤ T₀(4M+s) ≤ 3·T₀(M) + 2`   (`s < 4`)

by iterating it: subtracting `1` turns the lower bound into
`T₀(4M+s) - 1 ≥ 3·(T₀(M) - 1)`, adding `1` turns the upper bound into
`T₀(4M+s) + 1 ≤ 3·(T₀(M) + 1)`, and each base-four digit contributes
one factor of `3`.  Since `3 = 4^α`, a cutoff with `k` base-four digits
above the seed contributes `3^k = (4^k)^α`.

The iteration uses nothing about the residue sums beyond the bracket
and a seed, so it is stated for an **arbitrary integer sequence**
`U : ℕ → ℤ`:

* `two_le_of_step`, `three_pow_add_one_le_of_step` — the lower
  amplification: `U(N) ≥ 3·U(N/4) - 2` and `U ≥ 2` on the seed window
  `N₀ ≤ N < 4N₀` give `U(N) ≥ 3^k + 1` for `N ≥ N₀·4^k`.
* `add_one_le_two_mul_three_pow_of_step` — the upper amplification:
  `U(N) ≤ 3·U(N/4) + 2` and `U + 1 ≤ 2` below `4` give
  `U(N) + 1 ≤ 2·3^k` for `N < 4^(k+1)`.
* `rpow_div_le_of_three_pow_le`, `le_two_mul_rpow_of_add_one_le` — the
  conversion of both to the power law `N^(log₄3)`.

The residue class `r = 1` reuses all of this in
`ThueMorseNewmanResidues`.  For `T₀`:

* `two_le_thueMorseResidueSum_three_zero` — the seed `T₀(N) ≥ 2` for
  `N ≥ 4`.
* `three_pow_add_one_le_thueMorseResidueSum_three_zero` — the integer
  lower bound `T₀(N) ≥ 3^k + 1` for `N ≥ 4^(k+1)`.
* `thueMorseResidueSum_three_zero_add_one_le` — the integer upper bound
  `T₀(N) + 1 ≤ 2·3^k` for `N < 4^(k+1)`.
* `newman_lower_bound`, `newman_upper_bound` — **the quantitative
  Newman theorem**: for every `N ≥ 1`,

  `N^(log₄3) / 9 ≤ N₃(N) ≤ 2·N^(log₄3)`,

  with constants `1/9` and `2` that improve Newman's `1/20` and `5`
  (numerically the ratio `N₃(N)/N^α` ranges over `[0.418…, 1]` for
  `N < 2^16`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Amplification along base-four digits, for any sequence -/

/-- **Seed propagation**: if `U(N) ≥ 3·U(N/4) - 2` for all `N` and
`U ≥ 2` on the window `N₀ ≤ N < 4N₀`, then `U ≥ 2` for all `N ≥ N₀`. -/
theorem two_le_of_step {U : ℕ → ℤ} {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hstep : ∀ N, 3 * U (N / 4) - 2 ≤ U N)
    (hseed : ∀ N, N₀ ≤ N → N < 4 * N₀ → 2 ≤ U N) :
    ∀ N, N₀ ≤ N → 2 ≤ U N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases h : N < 4 * N₀
    · exact hseed N hN h
    · have hIH := ih (N / 4) (by omega) (by omega)
      linarith [hstep N]

/-- **Lower amplification**: under the same hypotheses,
`U(N) ≥ 3^k + 1` whenever `N ≥ N₀·4^k`.  Each base-four digit above
the seed multiplies `U - 1` by at least three. -/
theorem three_pow_add_one_le_of_step {U : ℕ → ℤ} {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hstep : ∀ N, 3 * U (N / 4) - 2 ≤ U N)
    (hseed : ∀ N, N₀ ≤ N → N < 4 * N₀ → 2 ≤ U N) (k : ℕ) :
    ∀ N, N₀ * 4 ^ k ≤ N → (3 : ℤ) ^ k + 1 ≤ U N := by
  induction k with
  | zero =>
      intro N hN
      have := two_le_of_step hN₀ hstep hseed N (by simpa using hN)
      simpa using this
  | succ k ih =>
      intro N hN
      have hM : N₀ * 4 ^ k ≤ N / 4 := by
        rw [show N₀ * 4 ^ (k + 1) = 4 * (N₀ * 4 ^ k) by ring] at hN
        omega
      have hIH := ih (N / 4) hM
      have := hstep N
      rw [pow_succ]
      linarith

/-- **Upper amplification**: if `U(N) ≤ 3·U(N/4) + 2` for all `N` and
`U + 1 ≤ 2` below `4`, then `U(N) + 1 ≤ 2·3^k` whenever `N < 4^(k+1)`.
Each base-four digit multiplies `U + 1` by at most three. -/
theorem add_one_le_two_mul_three_pow_of_step {U : ℕ → ℤ}
    (hstep : ∀ N, U N ≤ 3 * U (N / 4) + 2)
    (hseed : ∀ N, N < 4 → U N + 1 ≤ 2) (k : ℕ) :
    ∀ N, N < 4 ^ (k + 1) → U N + 1 ≤ 2 * (3 : ℤ) ^ k := by
  induction k with
  | zero =>
      intro N hN
      simpa using hseed N (by simpa using hN)
  | succ k ih =>
      intro N hN
      have hM : N / 4 < 4 ^ (k + 1) := by
        rw [pow_succ] at hN
        omega
      have hIH := ih (N / 4) hM
      have := hstep N
      rw [pow_succ]
      linarith

/-! ## The power law -/

/-- `(4^j)^(log₄3) = 3^j`. -/
theorem four_pow_rpow_logb_four_three (j : ℕ) :
    ((4 : ℝ) ^ j) ^ (Real.logb 4 3) = (3 : ℝ) ^ j := by
  have h43 : (4 : ℝ) ^ (Real.logb 4 3) = 3 :=
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), h43, Real.rpow_natCast]

/-- **From integer amplification to the power law, lower form**: if
`U(N) ≥ 3^k + 1` for `N ≥ N₀·4^k`, then
`U(N) ≥ N^(log₄3) / (3·N₀^(log₄3))` for every `N ≥ N₀`. -/
theorem rpow_div_le_of_three_pow_le {U : ℕ → ℤ} {N₀ : ℕ} (hN₀ : 0 < N₀)
    (h : ∀ k N, N₀ * 4 ^ k ≤ N → (3 : ℤ) ^ k + 1 ≤ U N) (N : ℕ)
    (hN : N₀ ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / (3 * (N₀ : ℝ) ^ (Real.logb 4 3)) ≤
      (U N : ℝ) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  set k := Nat.log 4 (N / N₀) with hk
  have hq : N / N₀ ≠ 0 := (Nat.div_pos hN hN₀).ne'
  have hlow : N₀ * 4 ^ k ≤ N := by
    have h1 : 4 ^ k ≤ N / N₀ := Nat.pow_log_le_self 4 hq
    calc N₀ * 4 ^ k ≤ N₀ * (N / N₀) := Nat.mul_le_mul_left _ h1
      _ ≤ N := Nat.mul_div_le N N₀
  have hhigh : N < N₀ * 4 ^ (k + 1) := by
    have h1 : N / N₀ < 4 ^ (k + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) _
    have h2 := Nat.lt_mul_of_div_lt h1 hN₀
    linarith
  have hcast : ((3 : ℝ) ^ k + 1 : ℝ) ≤ (U N : ℝ) := by
    exact_mod_cast h k N hlow
  have hreal : (N : ℝ) ^ (Real.logb 4 3) ≤
      (N₀ : ℝ) ^ (Real.logb 4 3) * 3 ^ (k + 1) := by
    have h1 : (N : ℝ) ^ (Real.logb 4 3) ≤
        ((N₀ * 4 ^ (k + 1) : ℕ) : ℝ) ^ (Real.logb 4 3) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhigh.le) hα
    push_cast at h1
    rwa [Real.mul_rpow (by positivity) (by positivity),
      four_pow_rpow_logb_four_three] at h1
  have hpos : (0 : ℝ) < 3 * (N₀ : ℝ) ^ (Real.logb 4 3) := by positivity
  rw [div_le_iff₀ hpos]
  have h3 : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
  nlinarith [hreal, hcast, h3, Real.rpow_nonneg (Nat.cast_nonneg N₀)
    (Real.logb 4 3)]

/-- **From integer amplification to the power law, upper form**: if
`U(N) + 1 ≤ 2·3^k` for `N < 4^(k+1)`, then `U(N) ≤ 2·N^(log₄3)` for
every `N ≥ 1`. -/
theorem le_two_mul_rpow_of_add_one_le {U : ℕ → ℤ}
    (h : ∀ k N, N < 4 ^ (k + 1) → U N + 1 ≤ 2 * (3 : ℤ) ^ k) (N : ℕ)
    (hN : 1 ≤ N) :
    (U N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  set k := Nat.log 4 N with hk
  have hlow : 4 ^ k ≤ N := Nat.pow_log_le_self 4 (by omega)
  have hhigh : N < 4 ^ (k + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) N
  have hreal : (3 : ℝ) ^ k ≤ (N : ℝ) ^ (Real.logb 4 3) := by
    rw [← four_pow_rpow_logb_four_three]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlow) hα
  have hcast : (U N : ℝ) + 1 ≤ 2 * (3 : ℝ) ^ k := by
    exact_mod_cast h k N hhigh
  linarith

/-! ## The residue class zero -/

/-- **The seed**: `T₀(N) ≥ 2` for every `N ≥ 4`.  On `4 ≤ N < 16` this
is read off the first sixteen signs (`T₀ = 2,2,2,3,3,3,4,4,4,5,5,5`);
beyond, the bracket gives `T₀(N) ≥ 3·2 - 2 = 4`. -/
theorem two_le_thueMorseResidueSum_three_zero : ∀ N : ℕ, 4 ≤ N →
    2 ≤ thueMorseResidueSum 3 0 N :=
  two_le_of_step (N₀ := 4) (by norm_num)
    (fun N => (thueMorseResidueSum_three_zero_bracket N).1)
    (fun N h1 h2 => by interval_cases N <;> decide)

/-- **Integer lower bound**: `T₀(N) ≥ 3^k + 1` whenever `N ≥ 4^(k+1)`.
Each base-four digit above the seed multiplies `T₀ - 1` by at least
three. -/
theorem three_pow_add_one_le_thueMorseResidueSum_three_zero (k : ℕ) :
    ∀ N : ℕ, 4 * 4 ^ k ≤ N →
      (3 : ℤ) ^ k + 1 ≤ thueMorseResidueSum 3 0 N :=
  three_pow_add_one_le_of_step (N₀ := 4) (by norm_num)
    (fun N => (thueMorseResidueSum_three_zero_bracket N).1)
    (fun N h1 h2 => by interval_cases N <;> decide) k

/-- **Integer upper bound**: `T₀(N) + 1 ≤ 2·3^k` whenever `N < 4^(k+1)`.
Each base-four digit multiplies `T₀ + 1` by at most three, starting
from `T₀(0..3) + 1 ≤ 2`. -/
theorem thueMorseResidueSum_three_zero_add_one_le (k : ℕ) :
    ∀ N : ℕ, N < 4 ^ (k + 1) →
      thueMorseResidueSum 3 0 N + 1 ≤ 2 * (3 : ℤ) ^ k :=
  add_one_le_two_mul_three_pow_of_step
    (fun N => (thueMorseResidueSum_three_zero_bracket N).2)
    (fun N hN => by
      rw [thueMorseResidueSum_three_zero_of_lt_four N hN]
      split_ifs <;> norm_num) k

/-- **The quantitative Newman theorem, lower bound**: for every
`N ≥ 1`, `N₃(N) ≥ N^(log₄3) / 9`.  (Newman's constant was `1/20`.) -/
theorem newman_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 9 ≤ (thueMorseResidueSum 3 0 N : ℝ) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  by_cases h4 : N < 4
  · -- `T₀ = 1` and `N^α ≤ 4^α = 3`
    rw [thueMorseResidueSum_three_zero_of_lt_four N h4, if_neg (by omega)]
    have hle : (N : ℝ) ^ (Real.logb 4 3) ≤ (4 : ℝ) ^ (Real.logb 4 3) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast h4.le) hα
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)] at hle
    push_cast
    linarith
  · have h := rpow_div_le_of_three_pow_le (N₀ := 4) (by norm_num)
      (fun k N hk => three_pow_add_one_le_thueMorseResidueSum_three_zero k N hk)
      N (by omega)
    have h9 : (3 : ℝ) * ((4 : ℕ) : ℝ) ^ (Real.logb 4 3) = 9 := by
      rw [Nat.cast_ofNat,
        Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    rwa [h9] at h

/-- **The quantitative Newman theorem, upper bound**: for every `N`,
`N₃(N) ≤ 2·N^(log₄3)`.  (Newman's constant was `5`.) -/
theorem newman_upper_bound (N : ℕ) :
    (thueMorseResidueSum 3 0 N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [thueMorseResidueSum_three_zero_of_lt_four 0 (by norm_num), if_pos rfl]
    push_cast
    positivity
  · exact le_two_mul_rpow_of_add_one_le
      (fun k N hk => thueMorseResidueSum_three_zero_add_one_le k N hk) N hN

/-- **The quantitative Newman theorem** (two-sided): for every `N ≥ 1`,
`N^(log₄3) / 9 ≤ N₃(N) ≤ 2·N^(log₄3)`. -/
theorem newman_quantitative (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 9 ≤ (thueMorseResidueSum 3 0 N : ℝ) ∧
      (thueMorseResidueSum 3 0 N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) :=
  ⟨newman_lower_bound N hN, newman_upper_bound N⟩

end Fabius
