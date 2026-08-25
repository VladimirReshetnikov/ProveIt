import FabiusFunction.PeriodicSmooth
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Closed form for the concrete Fabius saddle jets

`FabiusSaddleCoefficientRecurrence` introduces the periodic saddle jets by a
first-order recurrence.  Writing `L = Real.log 2`, `Psi = negativeLaplacePsi`
and `s n = negativeLaplaceJetSlope n = (-1)^(n+1) * n !`, that recurrence is

`p 0 = 1 / 2 + Psi' / L`,
`p (n+1) = (deriv (p n)) / L - (n+1) * p n + s n / L`.

Every coefficient of the all-orders small-argument expansion of the Fabius
function is built from these jets, but the recurrence leaves them implicit: to
read off the coefficient of `lambda ^ (-j)` one has to run `2 * j` differentiation
steps.  This module solves the recurrence.

Abbreviating the differentiation operator by `D`, the recurrence reads
`p (n+1) = (D / L - (n+1)) (p n) + s n / L`, and the operators `D / L - k`
commute with each other, because
`(D/L - j)(D/L - k) = D^2/L^2 - (j+k) D/L + j k` is symmetric in `j` and `k`.
Hence the homogeneous part of the solution is the falling-factorial operator
`∏ k ∈ Finset.Icc 1 n, (D / L - k)` applied to `p 0`, while the inhomogeneous
terms telescope: the constant `s j / L` is carried forward by
`∏ k ∈ Finset.Icc (j+2) n, (-k)`, and the resulting sum of reciprocals is a
harmonic number.  The outcome is

`p n t = (-1)^n * n ! * (1/2 + H n / L)
          + ∑ m ∈ Finset.range (n+1), c n m * Psi^(m+1) t / L^(m+1)`,

where `H n` is the `n`-th harmonic number and `c n m` is the coefficient of
`z ^ m` in `∏ k ∈ Finset.Icc 1 n, (z - k)`.  These are signed Stirling numbers
of the first kind shifted by one in each index, `c n m = s (n+1) (m+1)`, because
`z * ∏ k ∈ Icc 1 n, (z - k) = ∏ k ∈ Icc 0 n, (z - k)`.  The shift matters: `s n 0`
vanishes for `n ≥ 1`, while `c n 0 = (-1)^n * n !` is exactly the constant that
carries the harmonic-number term.  The bounded exponent jet used by the saddle expansion is
the same sum with the sign of the `1/2` reversed:

`d n t = (-1)^n * n ! * (H n / L - 1/2)
          + ∑ m ∈ Finset.range (n+1), c n m * Psi^(m+1) t / L^(m+1)`.

At `n = 1` this reproduces `negativeLaplacePeriodicJet_one`, whose weights
`(-1, 1)` are the coefficients of `z - 1`; at `n = 3` the weights are
`(-6, 11, -6, 1)` and the constant is `-3 - 11 / L`.

The consequence for the asymptotic expansion is that no coefficient is left
defined only by a recurrence.  Each one is a finite expression with rational
coefficients in `1 / L` and the derivatives `Psi', …, Psi^(n+1)` of the
centered periodic correction, and the Fourier coefficients of those derivatives
are known explicitly in terms of the Gamma and Riemann zeta functions.  In
particular the `m`-th weight carries `Psi^(m+1)`, whose `k`-th Fourier mode is
multiplied by `(2 * pi * i * k)^(m+1)`; this is the algebraic reason why the
oscillation of the successive expansion coefficients grows with their order
even though `Psi` itself is uniformly tiny.

The weights are introduced here by their own recurrence, which is what the
induction needs, and which is exactly the recurrence satisfied by the
coefficients of `∏ k ∈ Finset.Icc 1 n, (X - k)`.

For coefficientwise use, `negativeLaplaceJetStirling_succ` packages the
constant and interior branches into one all-index recurrence, while
`negativeLaplaceJetStirling_apply_zero` and the zero-index derivative-sum
lemmas record the two boundary values that recur in concrete calculations.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff

namespace Fabius

noncomputable section

/-- The weight of `Psi^(m+1) / L^(m+1)` in the closed form of the `n`-th saddle
jet.  It is the coefficient of `z ^ m` in `∏ k ∈ Finset.Icc 1 n, (z - k)`, a
shifted signed Stirling number of the first kind, `c n m = s (n+1) (m+1)`: the
recurrence below is exactly the coefficient recurrence of multiplying that
product by `z - (n+1)`.  Note `c n 0 = (-1)^n * n !`, unlike the unshifted
`s n 0`, which vanishes for `n ≥ 1`. -/
def negativeLaplaceJetStirling : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => -((n : ℝ) + 1) * negativeLaplaceJetStirling n 0
  | n + 1, m + 1 =>
      negativeLaplaceJetStirling n m -
        ((n : ℝ) + 1) * negativeLaplaceJetStirling n (m + 1)

/-- The empty product has constant coefficient one. -/
@[simp] theorem negativeLaplaceJetStirling_zero_zero :
    negativeLaplaceJetStirling 0 0 = 1 := rfl

/-- The empty product has no higher coefficients. -/
@[simp] theorem negativeLaplaceJetStirling_zero_succ (m : ℕ) :
    negativeLaplaceJetStirling 0 (m + 1) = 0 := rfl

/-- Constant term of the falling-factorial recurrence. -/
theorem negativeLaplaceJetStirling_succ_zero (n : ℕ) :
    negativeLaplaceJetStirling (n + 1) 0 =
      -((n : ℝ) + 1) * negativeLaplaceJetStirling n 0 := rfl

/-- Interior step of the falling-factorial recurrence. -/
theorem negativeLaplaceJetStirling_succ_succ (n m : ℕ) :
    negativeLaplaceJetStirling (n + 1) (m + 1) =
      negativeLaplaceJetStirling n m -
        ((n : ℝ) + 1) * negativeLaplaceJetStirling n (m + 1) := rfl

/-- Unified successor recurrence, including the constant-coefficient
boundary at `m = 0`. -/
theorem negativeLaplaceJetStirling_succ (n m : ℕ) :
    negativeLaplaceJetStirling (n + 1) m =
      (if m = 0 then 0 else negativeLaplaceJetStirling n (m - 1)) -
        ((n : ℝ) + 1) * negativeLaplaceJetStirling n m := by
  cases m with
  | zero =>
      rw [negativeLaplaceJetStirling_succ_zero]
      simp
      ring
  | succ m =>
      rw [negativeLaplaceJetStirling_succ_succ]
      simp

/-- The weights vanish above the degree of their polynomial. -/
theorem negativeLaplaceJetStirling_eq_zero (n : ℕ) :
    ∀ m : ℕ, n < m → negativeLaplaceJetStirling n m = 0 := by
  induction n with
  | zero =>
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact negativeLaplaceJetStirling_zero_succ k
  | succ n ih =>
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [negativeLaplaceJetStirling_succ_succ, ih k (by omega),
        ih (k + 1) (by omega)]
      ring

/-- The leading weight is one, so the `n`-th jet really does reach the
`(n+1)`-st derivative of the periodic correction. -/
theorem negativeLaplaceJetStirling_self (n : ℕ) :
    negativeLaplaceJetStirling n n = 1 := by
  induction n with
  | zero => exact negativeLaplaceJetStirling_zero_zero
  | succ n ih =>
      rw [negativeLaplaceJetStirling_succ_succ, ih,
        negativeLaplaceJetStirling_eq_zero n (n + 1) (by omega)]
      ring

/-- Closed form of the constant weight: it is the signed factorial
`(-1)^n n!`. -/
theorem negativeLaplaceJetStirling_apply_zero (n : ℕ) :
    negativeLaplaceJetStirling n 0 =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) := by
  induction n with
  | zero => norm_num [negativeLaplaceJetStirling]
  | succ n ih =>
      rw [negativeLaplaceJetStirling_succ_zero, ih,
        Nat.factorial_succ, pow_succ]
      push_cast
      ring

/-- The constant Stirling weight is the negative of the corresponding
Laplace-jet slope.  This identifies the constant terms of the two recurrences
without expanding either signed factorial downstream. -/
theorem negativeLaplaceJetStirling_apply_zero_eq_neg_slope (n : ℕ) :
    negativeLaplaceJetStirling n 0 = -negativeLaplaceJetSlope n := by
  rw [negativeLaplaceJetStirling_apply_zero, negativeLaplaceJetSlope,
    pow_succ]
  ring

/-- The `(m+1)`-st derivative of the centered periodic correction, normalized by
`(log 2) ^ (m+1)`.  Apart from `log 2` itself, these are the only
non-elementary quantities occurring in the closed-form jets: everything else in
them is rational. -/
def negativeLaplacePsiScaledDeriv (m : ℕ) (t : ℝ) : ℝ :=
  iteratedDeriv (m + 1) negativeLaplacePsi t / Real.log 2 ^ (m + 1)

/-- Zeroth normalized derivative: the first derivative of `Psi`, divided by
`log 2`. -/
theorem negativeLaplacePsiScaledDeriv_zero (t : ℝ) :
    negativeLaplacePsiScaledDeriv 0 t =
      deriv negativeLaplacePsi t / Real.log 2 := by
  simp [negativeLaplacePsiScaledDeriv, iteratedDeriv_one]

/-- Differentiating the `m`-th iterated derivative gives the `(m+1)`-st. -/
theorem negativeLaplacePsi_iteratedDeriv_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv m negativeLaplacePsi)
      (iteratedDeriv (m + 1) negativeLaplacePsi t) t := by
  have h := ((contDiff_infty_iteratedDeriv_negativeLaplacePsi m).differentiable
    (by simp) t).hasDerivAt
  simpa only [iteratedDeriv_succ] using h

/-- The normalized derivatives are one-periodic. -/
theorem negativeLaplacePsiScaledDeriv_periodic (m : ℕ) :
    Function.Periodic (negativeLaplacePsiScaledDeriv m) 1 := by
  intro t
  unfold negativeLaplacePsiScaledDeriv
  rw [negativeLaplacePsi_iteratedDeriv_periodic (m + 1) t]

/-- Differentiating a normalized derivative multiplies by `log 2` and advances
the index. -/
theorem negativeLaplacePsiScaledDeriv_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (negativeLaplacePsiScaledDeriv m)
      (Real.log 2 * negativeLaplacePsiScaledDeriv (m + 1) t) t := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h := (negativeLaplacePsi_iteratedDeriv_hasDerivAt (m + 1) t).div_const
    (Real.log 2 ^ (m + 1))
  have hval : iteratedDeriv (m + 1 + 1) negativeLaplacePsi t /
        Real.log 2 ^ (m + 1) =
      Real.log 2 * negativeLaplacePsiScaledDeriv (m + 1) t := by
    unfold negativeLaplacePsiScaledDeriv
    field_simp
    ring
  rw [← hval]
  exact h

/-- The Stirling-weighted derivative sum in the closed-form jets. -/
def negativeLaplaceJetDerivativeSum (n : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    negativeLaplaceJetStirling n m * negativeLaplacePsiScaledDeriv m t

/-- The same weighted sum with every derivative index advanced by one.  It is
the value of `deriv (negativeLaplaceJetDerivativeSum n) / log 2`. -/
def negativeLaplaceJetShiftedSum (n : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    negativeLaplaceJetStirling n m * negativeLaplacePsiScaledDeriv (m + 1) t

/-- At jet order zero the derivative sum consists only of its zeroth
normalized derivative. -/
theorem negativeLaplaceJetDerivativeSum_zero (t : ℝ) :
    negativeLaplaceJetDerivativeSum 0 t =
      negativeLaplacePsiScaledDeriv 0 t := by
  simp [negativeLaplaceJetDerivativeSum]

/-- At jet order zero the shifted sum consists only of the next normalized
derivative. -/
theorem negativeLaplaceJetShiftedSum_zero (t : ℝ) :
    negativeLaplaceJetShiftedSum 0 t =
      negativeLaplacePsiScaledDeriv 1 t := by
  simp [negativeLaplaceJetShiftedSum]

/-- The weighted sum is insensitive to enlarging its summation range. -/
theorem sum_range_negativeLaplaceJetStirling_eq (n N : ℕ) (hN : n + 1 ≤ N)
    (t : ℝ) :
    ∑ m ∈ Finset.range N,
        negativeLaplaceJetStirling n m * negativeLaplacePsiScaledDeriv m t =
      negativeLaplaceJetDerivativeSum n t := by
  unfold negativeLaplaceJetDerivativeSum
  refine (Finset.sum_subset (Finset.range_subset_range.2 hN) ?_).symm
  intro m _hm hmn
  have hlt : n < m := by
    simp only [Finset.mem_range, not_lt] at hmn
    omega
  rw [negativeLaplaceJetStirling_eq_zero n m hlt, zero_mul]

/-- The weighted sum is one-periodic. -/
theorem negativeLaplaceJetDerivativeSum_periodic (n : ℕ) :
    Function.Periodic (negativeLaplaceJetDerivativeSum n) 1 := by
  intro t
  unfold negativeLaplaceJetDerivativeSum
  exact Finset.sum_congr rfl fun m _ => by
    rw [negativeLaplacePsiScaledDeriv_periodic m t]

/-- Derivative of the weighted sum. -/
theorem negativeLaplaceJetDerivativeSum_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (negativeLaplaceJetDerivativeSum n)
      (Real.log 2 * negativeLaplaceJetShiftedSum n t) t := by
  have h : HasDerivAt
      (fun u => ∑ m ∈ Finset.range (n + 1),
        negativeLaplaceJetStirling n m * negativeLaplacePsiScaledDeriv m u)
      (∑ m ∈ Finset.range (n + 1),
        negativeLaplaceJetStirling n m *
          (Real.log 2 * negativeLaplacePsiScaledDeriv (m + 1) t)) t := by
    apply HasDerivAt.fun_sum
    intro m _hm
    exact HasDerivAt.const_mul _ (negativeLaplacePsiScaledDeriv_hasDerivAt m t)
  have hval : (∑ m ∈ Finset.range (n + 1),
        negativeLaplaceJetStirling n m *
          (Real.log 2 * negativeLaplacePsiScaledDeriv (m + 1) t)) =
      Real.log 2 * negativeLaplaceJetShiftedSum n t := by
    unfold negativeLaplaceJetShiftedSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [← hval]
  exact h

/-- One step of the falling-factorial recurrence at the level of weighted
sums. -/
theorem negativeLaplaceJetShiftedSum_sub (n : ℕ) (t : ℝ) :
    negativeLaplaceJetShiftedSum n t -
        ((n : ℝ) + 1) * negativeLaplaceJetDerivativeSum n t =
      negativeLaplaceJetDerivativeSum (n + 1) t := by
  have hbracket :
      (∑ i ∈ Finset.range (n + 1),
          negativeLaplaceJetStirling n (i + 1) *
            negativeLaplacePsiScaledDeriv (i + 1) t) +
        negativeLaplaceJetStirling n 0 * negativeLaplacePsiScaledDeriv 0 t =
      negativeLaplaceJetDerivativeSum n t := by
    rw [← sum_range_negativeLaplaceJetStirling_eq n (n + 2) (by omega) t]
    exact (Finset.sum_range_succ'
      (fun m => negativeLaplaceJetStirling n m *
        negativeLaplacePsiScaledDeriv m t) (n + 1)).symm
  have hsplit :
      negativeLaplaceJetDerivativeSum (n + 1) t =
        (∑ i ∈ Finset.range (n + 1),
            negativeLaplaceJetStirling (n + 1) (i + 1) *
              negativeLaplacePsiScaledDeriv (i + 1) t) +
          negativeLaplaceJetStirling (n + 1) 0 *
            negativeLaplacePsiScaledDeriv 0 t := by
    unfold negativeLaplaceJetDerivativeSum
    exact Finset.sum_range_succ'
      (fun m => negativeLaplaceJetStirling (n + 1) m *
        negativeLaplacePsiScaledDeriv m t) (n + 1)
  have hdistrib :
      ∑ i ∈ Finset.range (n + 1),
          (negativeLaplaceJetStirling n i -
            ((n : ℝ) + 1) * negativeLaplaceJetStirling n (i + 1)) *
            negativeLaplacePsiScaledDeriv (i + 1) t =
        negativeLaplaceJetShiftedSum n t -
          ((n : ℝ) + 1) *
            ∑ i ∈ Finset.range (n + 1),
              negativeLaplaceJetStirling n (i + 1) *
                negativeLaplacePsiScaledDeriv (i + 1) t := by
    unfold negativeLaplaceJetShiftedSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  simp only [negativeLaplaceJetStirling_succ_succ,
    negativeLaplaceJetStirling_succ_zero]
  rw [hdistrib, ← hbracket]
  ring

private theorem harmonic_succ_cast (n : ℕ) :
    ((harmonic (n + 1) : ℚ) : ℝ) =
      ((harmonic n : ℚ) : ℝ) + ((n : ℝ) + 1)⁻¹ := by
  rw [harmonic_succ]
  push_cast
  ring

/-- The constant part of the closed-form jet: it involves only the harmonic
numbers and `log 2`, and carries all the non-oscillatory content. -/
def negativeLaplaceJetConstant (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n.factorial : ℝ) *
    (1 / 2 + ((harmonic n : ℚ) : ℝ) / Real.log 2)

/-- The zeroth constant is `1/2`, matching `negativeLaplacePeriodicJet 0`. -/
@[simp] theorem negativeLaplaceJetConstant_zero :
    negativeLaplaceJetConstant 0 = 1 / 2 := by
  unfold negativeLaplaceJetConstant
  norm_num [harmonic_zero]

/-- The constant part obeys the inhomogeneous half of the jet recurrence. -/
theorem negativeLaplaceJetConstant_succ (n : ℕ) :
    negativeLaplaceJetConstant (n + 1) =
      -((n : ℝ) + 1) * negativeLaplaceJetConstant n +
        negativeLaplaceJetSlope n / Real.log 2 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hn1 : ((n : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  unfold negativeLaplaceJetConstant negativeLaplaceJetSlope
  rw [harmonic_succ_cast n, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- **Closed form for the periodic saddle jets.**  The recurrence of
`FabiusSaddleCoefficientRecurrence` is solved by a harmonic-number constant
together with a Stirling-weighted sum of normalized derivatives of the centered
periodic correction. -/
theorem negativeLaplacePeriodicJet_eq_closedForm (n : ℕ) : ∀ t : ℝ,
    negativeLaplacePeriodicJet n t =
      negativeLaplaceJetConstant n + negativeLaplaceJetDerivativeSum n t := by
  induction n with
  | zero =>
      intro t
      rw [negativeLaplacePeriodicJet_zero, negativeLaplaceJetConstant_zero,
        negativeLaplaceJetDerivativeSum_zero,
        negativeLaplacePsiScaledDeriv_zero]
  | succ n ih =>
      intro t
      have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hfun : negativeLaplacePeriodicJet n =
          fun u => negativeLaplaceJetConstant n +
            negativeLaplaceJetDerivativeSum n u := funext ih
      have hderiv : deriv (negativeLaplacePeriodicJet n) t =
          Real.log 2 * negativeLaplaceJetShiftedSum n t := by
        rw [hfun]
        exact ((negativeLaplaceJetDerivativeSum_hasDerivAt n t).const_add
          (negativeLaplaceJetConstant n)).deriv
      have hcancel : Real.log 2 * negativeLaplaceJetShiftedSum n t /
          Real.log 2 = negativeLaplaceJetShiftedSum n t := by
        field_simp
      simp only [negativeLaplacePeriodicJet]
      rw [hderiv, hcancel, ih t, ← negativeLaplaceJetShiftedSum_sub n t,
        negativeLaplaceJetConstant_succ n]
      ring

/-- **Closed form for the bounded exponent jets.**  These are the quantities
that enter the saddle exponent polynomials, and hence every coefficient of the
small-argument expansion. -/
theorem negativeLaplaceBoundedExponentJet_eq_closedForm (n : ℕ) (t : ℝ) :
    negativeLaplaceBoundedExponentJet n t =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
          (((harmonic n : ℚ) : ℝ) / Real.log 2 - 1 / 2) +
        negativeLaplaceJetDerivativeSum n t := by
  unfold negativeLaplaceBoundedExponentJet
  rw [negativeLaplacePeriodicJet_eq_closedForm n t]
  unfold negativeLaplaceJetConstant negativeLaplaceJetSlope
  rw [pow_succ]
  ring

end

end Fabius
