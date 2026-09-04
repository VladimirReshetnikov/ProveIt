import FabiusFunction.SharpGelfondBound
import FabiusFunction.RvachevFixedMantissaRay
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The sharp Gelfond bound on a periodic dyadic orbit

For the normalized dyadic sine product `Q_n(t) = ∏_{j<n} |2 sin(π 2^j t)|`,
the sharp Gelfond bound of `SharpGelfondBound` gives
`Q_{n+1}(t) ≤ 2 · √3^n` for every real `t`.  When the dyadic orbit of `t` is
periodic — `2^d t = t + z` for an integer `z` — the product over `q` periods
is the `q`-th power of the product over one period,
`Q_{qd}(t) = Q_d(t)^q`, and comparing the two bounds for large `q` removes
the loss of the factor `2/√3` entirely:

`Q_d(t) ≤ √3^d`.

This is the Spectra volume's "sharp periodic-orbit sine-product bound",
`A_{a,q}^{1/d} ≤ √3` for rational `t = a/q` with odd `q`; the statement here
is the general one — any real `t` whose orbit returns, with no rationality
hypothesis — and the rational case is the instance `t = a/q`,
`2^d ≡ 1 (mod q)`.

## The extraction lemma

The step from `x^q ≤ C · c^q` for all `q ≥ 1` to `x ≤ c` is its own lemma,
`le_of_pow_le_mul_pow`, with no trigonometric content: a constant `C` in
front of a `q`-th power cannot survive taking `q`-th roots.  It is the
"periodicity upgrades a global bound to a per-orbit bound" argument in the
form in which any other periodic-orbit estimate can reuse it.
-/

set_option autoImplicit false

open Finset Filter
open scoped Topology

namespace Fabius

/-- **Roots absorb constants.**  If `x^q ≤ C · c^q` for every `q ≥ 1`, with
`c > 0`, then `x ≤ c`: otherwise `(x/c)^q` exceeds every bound, including
`C`.  No sign condition on `x` or `C` is needed. -/
theorem le_of_pow_le_mul_pow {x c C : ℝ} (hc : 0 < c)
    (h : ∀ q : ℕ, 1 ≤ q → x ^ q ≤ C * c ^ q) : x ≤ c := by
  refine le_of_not_gt fun hlt => ?_
  have hρ : 1 < x / c := (one_lt_div hc).mpr hlt
  obtain ⟨q, hq⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_gt_atTop
    (max C 1)).exists
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      simp only [pow_zero] at hq
      linarith [le_max_right C 1]
    · exact h0
  have hbound : (x / c) ^ q ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hc q)]
    exact h q hq1
  linarith [le_max_left C 1]

/-- **The sharp Gelfond bound, normalized**: `Q_{n+1}(t) ≤ 2 · √3^n` for
every real `t`. -/
theorem normalizedDyadicSineProduct_succ_le (n : ℕ) (t : ℝ) :
    normalizedDyadicSineProduct (n + 1) t ≤ 2 * Real.sqrt 3 ^ n := by
  rw [normalizedDyadicSineProduct_eq_two_pow_mul]
  have h := abs_prod_sin_two_pow_le_sharp t n
  simp only [mul_assoc] at h
  calc (2 : ℝ) ^ (n + 1) * ∏ j ∈ range (n + 1), |Real.sin (Real.pi * ((2 : ℝ) ^ j * t))|
      ≤ (2 : ℝ) ^ (n + 1) * (Real.sqrt 3 / 2) ^ n :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * Real.sqrt 3 ^ n := by
        rw [div_pow, pow_succ]
        field_simp

/-- **The sharp bound on a periodic orbit.**  If `2^d t = t + z` for an
integer `z`, then `Q_d(t) ≤ √3^d`: the factor `2/√3` of the one-shot bound
disappears, because the bound over `q` periods is the `q`-th power of the
bound over one. -/
theorem normalizedDyadicSineProduct_le_sqrt_three_pow_of_dyadic_period
    (d : ℕ) (t : ℝ) (z : ℤ) (hperiod : (2 : ℝ) ^ d * t = t + (z : ℝ)) :
    normalizedDyadicSineProduct d t ≤ Real.sqrt 3 ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine le_of_pow_le_mul_pow (C := 2 / Real.sqrt 3) (pow_pos hs3 d) fun q hq => ?_
  -- `Q_d^q = Q_{qd}` by periodicity
  have hper := normalizedDyadicSineProduct_mul_add_of_dyadic_period q 0 d t z hperiod
  rw [add_zero, normalizedDyadicSineProduct_zero, mul_one] at hper
  -- and `Q_{qd} ≤ 2 √3^{qd-1} = (2/√3) (√3^d)^q`
  have hqd : 1 ≤ q * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd.ne')
  have hle := normalizedDyadicSineProduct_succ_le (q * d - 1) t
  rw [Nat.sub_add_cancel hqd] at hle
  rw [← hper]
  calc normalizedDyadicSineProduct (q * d) t
      ≤ 2 * Real.sqrt 3 ^ (q * d - 1) := hle
    _ = 2 / Real.sqrt 3 * (Real.sqrt 3 ^ d) ^ q := by
        rw [← pow_mul, mul_comm d q]
        have : Real.sqrt 3 ^ (q * d) = Real.sqrt 3 ^ (q * d - 1) * Real.sqrt 3 := by
          rw [← pow_succ, Nat.sub_add_cancel hqd]
        rw [this]
        field_simp

end Fabius
