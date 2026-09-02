import FabiusFunction.SharpGelfondBound
import FabiusFunction.ThueMorseSineProduct
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Gelfond's uniform bound, its attainment, and the arbitrary-length form

The atlas's `eq:gelfond-upper`, previously a literature citation
(Gelfond 1968): the Thue–Morse trigonometric polynomial obeys the
sharp uniform bound

`sup_x |∑_{n<2^m} ε(n)·e^(inx)| ≤ (2/√3)·3^(m/2) = 2·(√3)^(m-1)`,

so `log₄3` is the optimal uniform growth exponent of Thue–Morse
exponential sums.

The analytic content is the **two-step subaction** already formalized
abstractly in `SharpGelfondBound`: for `φ(t) = 2·|sin t|`,
`φ(t)²·φ(2t) ≤ 3√3` (`abs_sin_sq_mul_abs_sin_two_mul_le`), and the
two-step product principle `prod_le_pow_of_sq_mul_succ_le` telescopes
it along the doubling orbit.  This file only *instantiates* that
principle; the Thue–Morse content is the sine-product identity
`sum_thueMorseSign_exp_eq_sin_prod`, whose modulus is isolated once in
`norm_sum_thueMorseSign_exp` and then reused three times.

* `two_abs_sin_sq_mul_le` — the Gelfond inequality `φ(t)²·φ(2t) ≤ √27`
  in the atlas's normalization (`eq:gelfond-key`).
* `norm_sum_thueMorseSign_exp` — **the modulus of the dyadic Thue–Morse
  exponential sum is the sine product** `∏_{j<m} 2|sin(2^j·x/2)|`, for
  every real `x` and every `m` (`eq:finite-Fourier-magnitude`).
* `gelfond_prod_le_succ`, `gelfond_prod_le` — the telescoped product
  bound `∏_{j≤n} φ(2^j·θ) ≤ 2·(√3)^n`, with and without natural
  subtraction.
* `gelfond_uniform_bound` — **the uniform exponential-sum bound**
  (`eq:gelfond-upper`).
* `norm_sum_thueMorseSign_exp_two_pi_div_three` — **attainment**: at
  `x = 2π/3` the modulus is exactly `(√3)^m = 3^(m/2)`
  (`eq:gelfond-lower`), so the exponent `log₄3` cannot be lowered and
  the constant `2/√3` cannot drop below `1`.
* `gelfond_general_bound`, `gelfond_general_bound_rpow` — **the
  arbitrary-length bound** (`eq:gelfond-general`): for every `N`,
  `|∑_{n<N} ε(n)·e^(inx)| ≤ (√3+1)·(√3)^⌊log₂N⌋ ≤ (√3+1)·N^(log₄3)`,
  by splitting `[0,N)` at its top binary digit; the constant `√3+1` is
  exactly the one that makes the digit-by-digit induction close.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `√27 = (√3)³`. -/
theorem sqrt_twentyseven : Real.sqrt 27 = Real.sqrt 3 ^ 3 := by
  have h : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [h, show (27 : ℝ) = 9 * 3 by norm_num,
    Real.sqrt_mul (by norm_num) 3,
    show Real.sqrt 9 = 3 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]

/-- **The Gelfond inequality** in the atlas's normalization:
`(2|sin t|)²·(2|sin 2t|) ≤ √27`, tight at `t = π/3`.  It is the sharp
two-step inequality `|sin t|²·|sin 2t| ≤ (√3/2)³` of
`SharpGelfondBound` scaled by `8`. -/
theorem two_abs_sin_sq_mul_le (t : ℝ) :
    (2 * |Real.sin t|) ^ 2 * (2 * |Real.sin (2 * t)|) ≤
      Real.sqrt 27 := by
  have h := abs_sin_sq_mul_abs_sin_two_mul_le t
  calc (2 * |Real.sin t|) ^ 2 * (2 * |Real.sin (2 * t)|)
      = (|Real.sin t| ^ 2 * |Real.sin (2 * t)|) * 8 := by ring
    _ ≤ (Real.sqrt 3 / 2) ^ 3 * 8 :=
        mul_le_mul_of_nonneg_right h (by norm_num)
    _ = Real.sqrt 27 := by rw [sqrt_twentyseven]; ring

/-- **The modulus of the dyadic Thue–Morse exponential sum is a sine
product**: for every real `x` and every `m`,
`‖∑_{n<2^m} ε(n)·e^(inx)‖ = ∏_{j<m} 2·|sin(2^j·(x/2))|`. -/
theorem norm_sum_thueMorseSign_exp (x : ℝ) (m : ℕ) :
    ‖∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n‖ =
      ∏ j ∈ range m, (2 * |Real.sin (2 ^ j * (x / 2))|) := by
  rw [sum_thueMorseSign_exp_eq_sin_prod x m, norm_mul, norm_mul,
    norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hnegI : ‖(-2 * Complex.I : ℂ)‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    simp
  rw [hnegI, Complex.norm_prod]
  have hterm : ∀ j ∈ range m, ‖((Real.sin (2 ^ j * x / 2) : ℝ) : ℂ)‖ =
      |Real.sin (2 ^ j * (x / 2))| := by
    intro j _
    rw [Complex.norm_real, Real.norm_eq_abs,
      show (2 : ℝ) ^ j * x / 2 = 2 ^ j * (x / 2) by ring]
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
    Finset.prod_const, card_range]

/-- **The telescoped Gelfond product bound**, `n+1` factors and no
natural subtraction: `∏_{j≤n} 2|sin(2^j·θ)| ≤ 2·(√3)^n`.  This is the
two-step product principle of `SharpGelfondBound` applied to
`s j = |sin(2^j·θ)|`, `c = √3/2`, then rescaled by `2^(n+1)`. -/
theorem gelfond_prod_le_succ (θ : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), (2 * |Real.sin (2 ^ j * θ)|) ≤
      2 * Real.sqrt 3 ^ n := by
  have h : ∏ j ∈ range (n + 1), |Real.sin (2 ^ j * θ)| ≤
      (Real.sqrt 3 / 2) ^ n :=
    prod_le_pow_of_sq_mul_succ_le (s := fun j => |Real.sin (2 ^ j * θ)|)
      (fun j => abs_nonneg _) (fun j => Real.abs_sin_le_one _)
      (by positivity)
      (fun j => by
        have hj := abs_sin_sq_mul_abs_sin_two_mul_le (2 ^ j * θ)
        rwa [show 2 * (2 ^ j * θ) = 2 ^ (j + 1) * θ by ring] at hj) n
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_range]
  calc (2 : ℝ) ^ (n + 1) * ∏ j ∈ range (n + 1), |Real.sin (2 ^ j * θ)|
      ≤ 2 ^ (n + 1) * (Real.sqrt 3 / 2) ^ n :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * Real.sqrt 3 ^ n := by
        rw [div_pow, pow_succ]
        field_simp

/-- **The telescoped Gelfond product bound** in the atlas's form: for
`m ≥ 1`, `∏_{j<m} 2|sin(2^j·θ)| ≤ 2·(√3)^(m-1)`. -/
theorem gelfond_prod_le (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∏ j ∈ range m, (2 * |Real.sin (2 ^ j * θ)|) ≤
      2 * Real.sqrt 3 ^ (m - 1) := by
  obtain ⟨K, rfl⟩ : ∃ K, m = K + 1 := ⟨m - 1, by omega⟩
  simpa using gelfond_prod_le_succ θ K

/-- **Gelfond's uniform bound** (`eq:gelfond-upper`): for every real
`x` and `m ≥ 1`,
`|∑_{n<2^m} ε(n)·e^(inx)| ≤ 2·(√3)^(m-1) = (2/√3)·3^(m/2)`. -/
theorem gelfond_uniform_bound (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ‖∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n‖ ≤
      2 * Real.sqrt 3 ^ (m - 1) := by
  rw [norm_sum_thueMorseSign_exp]
  exact gelfond_prod_le (x / 2) m hm

/-- **Attainment** (`eq:gelfond-lower`): at the Gelfond frequency
`x = 2π/3` every sine factor has modulus `√3/2`, so
`‖∑_{n<2^m} ε(n)·e^(inx)‖ = (√3)^m = 3^(m/2)` exactly.  Hence the
supremum over `x` is at least `3^(m/2)`: the exponent `log₄3` of
`gelfond_uniform_bound` is optimal and its constant `2/√3` cannot be
replaced by anything below `1`. -/
theorem norm_sum_thueMorseSign_exp_two_pi_div_three (m : ℕ) :
    ‖∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) ^ n‖ =
      Real.sqrt 3 ^ m := by
  rw [norm_sum_thueMorseSign_exp]
  have h : ∀ j ∈ range m,
      2 * |Real.sin (2 ^ j * (2 * Real.pi / 3 / 2))| = Real.sqrt 3 := by
    intro j _
    rw [show (2 : ℝ) ^ j * (2 * Real.pi / 3 / 2) =
        Real.pi * 2 ^ j * (1 / 3) by ring, abs_sin_two_pow_third]
    ring
  rw [Finset.prod_congr rfl h, Finset.prod_const, card_range]

/-- The one-digit induction step behind `gelfond_general_bound`: for
every `N < 2^(L+1)`, `‖∑_{n<N} ε(n)·e^(inx)‖ ≤ (√3+1)·(√3)^L`.  Either
`N < 2^L` (use the previous level and `√3 ≥ 1`), or `N = 2^L + r` with
`r < 2^L`, and the tail `∑_{n<r} ε(2^L+n)·e^(i(2^L+n)x)` is
`-e^(i2^Lx)` times the sum of length `r`, because `ε(2^L+n) = -ε(n)`
below the top digit; the head is bounded by `gelfond_uniform_bound`
and the tail by the previous level, and `2·(√3)^(L-1) + (√3+1)(√3)^(L-1)
= (√3+1)(√3)^L` closes the induction. -/
theorem norm_sum_thueMorseSign_exp_le_of_lt_two_pow (x : ℝ) (L : ℕ) :
    ∀ N, N < 2 ^ (L + 1) →
      ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp ((x : ℂ) * Complex.I) ^ n‖ ≤
        (Real.sqrt 3 + 1) * Real.sqrt 3 ^ L := by
  have hs3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  induction L with
  | zero =>
      intro N hN
      have hN' : N = 0 ∨ N = 1 := by omega
      rcases hN' with rfl | rfl
      · rw [range_zero, sum_empty, norm_zero]
        positivity
      · simp [thueMorseSign, binaryWeight] <;> linarith
  | succ L ih =>
      intro N hN
      by_cases hlt : N < 2 ^ (L + 1)
      · calc ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) *
              Complex.exp ((x : ℂ) * Complex.I) ^ n‖
            ≤ (Real.sqrt 3 + 1) * Real.sqrt 3 ^ L := ih N hlt
          _ ≤ (Real.sqrt 3 + 1) * Real.sqrt 3 ^ (L + 1) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact pow_le_pow_right₀ hs3 (Nat.le_succ L)
      · obtain ⟨r, rfl⟩ : ∃ r, N = 2 ^ (L + 1) + r :=
          ⟨N - 2 ^ (L + 1), by omega⟩
        have hr : r < 2 ^ (L + 1) := by
          rw [pow_succ] at hN
          omega
        -- the tail is `-e^(i·2^(L+1)·x)` times the sum of length `r`
        have htail : ∑ n ∈ range r,
            ((thueMorseSign (2 ^ (L + 1) + n) : ℤ) : ℂ) *
              Complex.exp ((x : ℂ) * Complex.I) ^ (2 ^ (L + 1) + n) =
            -(Complex.exp ((x : ℂ) * Complex.I) ^ (2 ^ (L + 1)) *
              ∑ n ∈ range r, ((thueMorseSign n : ℤ) : ℂ) *
                Complex.exp ((x : ℂ) * Complex.I) ^ n) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun n hn => ?_
          have hn' : n < 2 ^ (L + 1) := lt_of_lt_of_le (mem_range.1 hn) hr.le
          have hsign : thueMorseSign (2 ^ (L + 1) + n) = -thueMorseSign n := by
            rw [thueMorseSign, thueMorseSign,
              binaryWeight_add_pow_two (L + 1) n hn', pow_succ]
            ring
          rw [hsign, pow_add]
          push_cast
          ring
        have hhead := gelfond_uniform_bound x (L + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hhead
        have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
          Real.mul_self_sqrt (by norm_num)
        rw [Finset.sum_range_add, htail]
        calc ‖(∑ n ∈ range (2 ^ (L + 1)), ((thueMorseSign n : ℤ) : ℂ) *
                Complex.exp ((x : ℂ) * Complex.I) ^ n) +
              -(Complex.exp ((x : ℂ) * Complex.I) ^ (2 ^ (L + 1)) *
                ∑ n ∈ range r, ((thueMorseSign n : ℤ) : ℂ) *
                  Complex.exp ((x : ℂ) * Complex.I) ^ n)‖
            ≤ ‖∑ n ∈ range (2 ^ (L + 1)), ((thueMorseSign n : ℤ) : ℂ) *
                Complex.exp ((x : ℂ) * Complex.I) ^ n‖ +
              ‖-(Complex.exp ((x : ℂ) * Complex.I) ^ (2 ^ (L + 1)) *
                ∑ n ∈ range r, ((thueMorseSign n : ℤ) : ℂ) *
                  Complex.exp ((x : ℂ) * Complex.I) ^ n)‖ := norm_add_le _ _
          _ = ‖∑ n ∈ range (2 ^ (L + 1)), ((thueMorseSign n : ℤ) : ℂ) *
                Complex.exp ((x : ℂ) * Complex.I) ^ n‖ +
              ‖∑ n ∈ range r, ((thueMorseSign n : ℤ) : ℂ) *
                Complex.exp ((x : ℂ) * Complex.I) ^ n‖ := by
              rw [norm_neg, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I,
                one_pow, one_mul]
          _ ≤ 2 * Real.sqrt 3 ^ L + (Real.sqrt 3 + 1) * Real.sqrt 3 ^ L :=
              add_le_add hhead (ih r hr)
          _ = (Real.sqrt 3 + 1) * Real.sqrt 3 ^ (L + 1) := by
              rw [pow_succ]
              linear_combination (-(Real.sqrt 3 ^ L)) * h3

/-- **Gelfond's bound for every length** (`eq:gelfond-general`): for
every real `x` and every `N`,
`‖∑_{n<N} ε(n)·e^(inx)‖ ≤ (√3+1)·(√3)^⌊log₂N⌋`, uniformly in `x`.
The right-hand side is `(√3+1)·(2^⌊log₂N⌋)^(log₄3) ≤ (√3+1)·N^(log₄3)`;
see `gelfond_general_bound_rpow`. -/
theorem gelfond_general_bound (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n‖ ≤
      (Real.sqrt 3 + 1) * Real.sqrt 3 ^ Nat.log 2 N :=
  norm_sum_thueMorseSign_exp_le_of_lt_two_pow x (Nat.log 2 N) N
    (Nat.lt_pow_succ_log_self one_lt_two N)

/-- `2^(log₄3) = √3`: the Gelfond growth exponent `log₄3` is the
base-`2` logarithm of `√3`. -/
theorem two_rpow_logb_four_three :
    (2 : ℝ) ^ (Real.logb 4 3) = Real.sqrt 3 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.logb,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  congr 1
  push_cast
  rw [mul_div_assoc', mul_comm (Real.log 2), mul_div_mul_right _ _ h2,
    mul_one_div]

/-- **Gelfond's bound for every length, power-law form**
(`eq:gelfond-general`): `‖∑_{n<N} ε(n)·e^(inx)‖ ≤ (√3+1)·N^(log₄3)` for
every real `x` and every `N`, so `log₄3` is the uniform growth exponent
of Thue–Morse exponential sums, and by
`norm_sum_thueMorseSign_exp_two_pi_div_three` it is optimal. -/
theorem gelfond_general_bound_rpow (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n‖ ≤
      (Real.sqrt 3 + 1) * (N : ℝ) ^ (Real.logb 4 3) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [range_zero, sum_empty, norm_zero]
    positivity
  · refine (gelfond_general_bound x N).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlog : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
    have e1 : (2 : ℝ) ^ Nat.log 2 N = (2 : ℝ) ^ (Nat.log 2 N : ℝ) :=
      (Real.rpow_natCast 2 _).symm
    have e2 : Real.sqrt 3 ^ Nat.log 2 N = Real.sqrt 3 ^ (Nat.log 2 N : ℝ) :=
      (Real.rpow_natCast _ _).symm
    calc Real.sqrt 3 ^ Nat.log 2 N
        = ((2 : ℝ) ^ Nat.log 2 N) ^ (Real.logb 4 3) := by
          rw [e1, e2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← two_rpow_logb_four_three,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      _ ≤ (N : ℝ) ^ (Real.logb 4 3) := by
          refine Real.rpow_le_rpow (pow_nonneg (by norm_num) _) ?_ hlog
          exact_mod_cast Nat.pow_log_le_self 2 hN.ne'

end Fabius
