import FabiusFunction.BernoulliRecurrences
import FabiusFunction.CenteredMomentCumulants
import FabiusFunction.DyadicClosedForm
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# The Bernoulli logarithm of the hyperbolic-sine quotient

This module closes the Bernoulli--Mersenne frontier left explicit in
`CenteredMomentCumulants`.  Everything is formal and coefficientwise.  The
finite identity at the heart of the proof is

`sum r=1..n+1, 2^(2*r-1) * choose (2*n+3) (2*r) * B_(2*r) = n+1`.

It is the odd Bernoulli polynomial `B_(2*n+3)` evaluated at `1/2`: reflection
about `1/2` makes that value zero, while all odd Bernoulli numbers beyond
`B_1` vanish.  After division by `(2*n+3)!`, this finite identity says exactly

`sinhDivPS * (bernoulli logarithm)' = (sinhDivPS)'`.

The uniqueness theorem for the recursively defined formal logarithm then
identifies every positive coefficient, without an analytic logarithm,
convergence, or a choice of branch.  As consequences, the centered Rvachev
cumulants have the Bernoulli--Mersenne form in every even order and the
spectral report's moment recurrence is unconditional.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius

noncomputable section

/-! ## The finite Bernoulli identity -/

/-- Every odd Bernoulli polynomial vanishes at the reflection fixed point
`1/2`.  This rational statement is a direct consequence of polynomial
reflection, not an analytic generating-function argument. -/
theorem bernoulliPolynomial_odd_eval_half (n : ℕ) :
    (Polynomial.bernoulli (2 * n + 1)).eval (1 / 2 : ℚ) = 0 := by
  have hreflect :=
    Polynomial.bernoulli_eval_one_sub (2 * n + 1) (1 / 2 : ℚ)
  have harg : (1 : ℚ) - 1 / 2 = 1 / 2 := by norm_num
  have hsign : (-1 : ℚ) ^ (2 * n + 1) = -1 := by
    norm_num [pow_add, pow_mul]
  rw [harg, hsign] at hreflect
  linarith

private def weightedBernoulliTerm (m k : ℕ) : ℚ :=
  (2 : ℚ) ^ k * (Nat.choose m k : ℚ) * bernoulli k

/-- The half-argument identity for an odd Bernoulli polynomial, cleared of
powers of two. -/
private theorem weightedBernoulliSum_odd (n : ℕ) :
    ∑ k ∈ range (2 * n + 4), weightedBernoulliTerm (2 * n + 3) k = 0 := by
  let m := 2 * n + 3
  have hhalf : (Polynomial.bernoulli m).eval (1 / 2 : ℚ) = 0 := by
    change (Polynomial.bernoulli (2 * n + 3)).eval (1 / 2 : ℚ) = 0
    have hindex : 2 * n + 3 = 2 * (n + 1) + 1 := by omega
    rw [hindex]
    exact bernoulliPolynomial_odd_eval_half (n + 1)
  simp only [Polynomial.bernoulli, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial] at hhalf
  have hscaled := congrArg (fun q : ℚ => (2 : ℚ) ^ m * q) hhalf
  rw [mul_zero, Finset.mul_sum] at hscaled
  have hterm (k : ℕ) (hk : k ∈ range (m + 1)) :
      (2 : ℚ) ^ m *
          ((bernoulli k * (Nat.choose m k : ℚ)) *
            (1 / 2 : ℚ) ^ (m - k)) =
        weightedBernoulliTerm m k := by
    have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.1 hk)
    have hden : (2 : ℚ) ^ (m - k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hratio :
        (2 : ℚ) ^ m / (2 : ℚ) ^ (m - k) = (2 : ℚ) ^ k := by
      apply (div_eq_iff hden).2
      rw [mul_comm, pow_sub_mul_pow _ hkm]
    rw [one_div_pow]
    calc
      (2 : ℚ) ^ m *
            ((bernoulli k * (Nat.choose m k : ℚ)) *
              (1 / (2 : ℚ) ^ (m - k))) =
          (bernoulli k * (Nat.choose m k : ℚ)) *
            ((2 : ℚ) ^ m / (2 : ℚ) ^ (m - k)) := by ring
      _ = weightedBernoulliTerm m k := by
        rw [hratio]
        simp only [weightedBernoulliTerm]
        ring
  change ∑ k ∈ range (m + 1), weightedBernoulliTerm m k = 0
  calc
    ∑ k ∈ range (m + 1), weightedBernoulliTerm m k =
        ∑ k ∈ range (m + 1),
          (2 : ℚ) ^ m *
            ((bernoulli k * (Nat.choose m k : ℚ)) *
              (1 / 2 : ℚ) ^ (m - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hterm k hk).symm
    _ = 0 := hscaled

/-- The exact finite Bernoulli identity needed by the logarithmic derivative
of `sinh(√X)/√X`. -/
theorem weightedEvenBernoulliChooseSum (n : ℕ) :
    (∑ k ∈ range (n + 1),
        (2 : ℚ) ^ (2 * (k + 1) - 1) *
          (Nat.choose (2 * n + 3) (2 * (k + 1)) : ℚ) *
          bernoulli (2 * (k + 1))) = n + 1 := by
  let m := 2 * n + 3
  let f : ℕ → ℚ := weightedBernoulliTerm m
  have hfull : ∑ k ∈ range (2 * (n + 2)), f k = 0 := by
    have hrange : 2 * (n + 2) = 2 * n + 4 := by omega
    rw [hrange]
    simpa [m, f] using weightedBernoulliSum_odd n
  have hodd (k : ℕ) (hk : k ∈ range (n + 2)) (hk0 : k ≠ 0) :
      f (2 * k + 1) = 0 := by
    have hOdd : Odd (2 * k + 1) := ⟨k, by omega⟩
    have hgt : 1 < 2 * k + 1 := by omega
    simp only [f, weightedBernoulliTerm]
    rw [bernoulli_eq_zero_of_odd hOdd hgt]
    ring
  have hoddSum :
      (∑ k ∈ range (n + 2), f (2 * k + 1)) = -(m : ℚ) := by
    calc
      ∑ k ∈ range (n + 2), f (2 * k + 1) = f 1 := by
        apply Finset.sum_eq_single 0
        · intro k hk hk0
          exact hodd k hk hk0
        · intro hnot
          exact (hnot (by simp)).elim
      _ = -(m : ℚ) := by
        simp [f, weightedBernoulliTerm, bernoulli_one, m]
        ring
  have hsplit := sum_range_two_mul (n + 2) f
  rw [Finset.sum_add_distrib, hoddSum] at hsplit
  have heven : ∑ k ∈ range (n + 2), f (2 * k) = (m : ℚ) := by
    linear_combination hfull - hsplit
  rw [Finset.sum_range_succ'] at heven
  have hf0 : f 0 = 1 := by
    simp [f, weightedBernoulliTerm]
  rw [hf0] at heven
  let S : ℚ := ∑ k ∈ range (n + 1),
    (2 : ℚ) ^ (2 * (k + 1) - 1) *
      (Nat.choose (2 * n + 3) (2 * (k + 1)) : ℚ) *
      bernoulli (2 * (k + 1))
  have hterm (k : ℕ) :
      f (2 * (k + 1)) =
        2 * ((2 : ℚ) ^ (2 * (k + 1) - 1) *
          (Nat.choose (2 * n + 3) (2 * (k + 1)) : ℚ) *
          bernoulli (2 * (k + 1))) := by
    have hexp : 2 * (k + 1) = (2 * (k + 1) - 1) + 1 := by omega
    have hpow : (2 : ℚ) ^ (2 * (k + 1)) =
        2 * (2 : ℚ) ^ (2 * (k + 1) - 1) := by
      calc
        (2 : ℚ) ^ (2 * (k + 1)) =
            (2 : ℚ) ^ ((2 * (k + 1) - 1) + 1) :=
          congrArg (fun e : ℕ => (2 : ℚ) ^ e) hexp
        _ = (2 : ℚ) ^ (2 * (k + 1) - 1) * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℚ) ^ (2 * (k + 1) - 1) := by ring
    simp only [f, weightedBernoulliTerm, m]
    rw [hpow]
    ring
  have hdouble : 2 * S = (2 : ℚ) * (n + 1 : ℚ) := by
    calc
      2 * S = ∑ k ∈ range (n + 1), f (2 * (k + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        exact (hterm k).symm
      _ = (m : ℚ) - 1 := by linarith
      _ = (2 : ℚ) * (n + 1 : ℚ) := by
        simp only [m]
        push_cast
        ring
  change S = (n + 1 : ℚ)
  linarith

/-! ## Formal logarithmic identification -/

private theorem sinhDiv_bernoulliLogDerivative_sum (n : ℕ) :
    (∑ k ∈ range (n + 1),
        sinhDivCoefficient (n - k) *
          ((k + 1 : ℚ) * bernoulliSinhDivLogCoefficient (k + 1))) =
      (n + 1 : ℚ) * sinhDivCoefficient (n + 1) := by
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      sinhDivCoefficient (n - k) *
          ((k + 1 : ℚ) * bernoulliSinhDivLogCoefficient (k + 1)) =
        ((2 : ℚ) ^ (2 * (k + 1) - 1) *
            (Nat.choose (2 * n + 3) (2 * (k + 1)) : ℚ) *
            bernoulli (2 * (k + 1))) /
          ((2 * n + 3).factorial : ℚ) := by
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
    have hk1 : k + 1 ≠ 0 := by omega
    have hk1q : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast hk1
    have hle : 2 * (k + 1) ≤ 2 * n + 3 := by omega
    have hsub : 2 * n + 3 - 2 * (k + 1) = 2 * (n - k) + 1 := by omega
    rw [sinhDivCoefficient, bernoulliSinhDivLogCoefficient,
      if_neg hk1, Nat.cast_choose ℚ hle, hsub]
    field_simp [hk1q]
    push_cast
    ring
  calc
    ∑ k ∈ range (n + 1),
          sinhDivCoefficient (n - k) *
            ((k + 1 : ℚ) * bernoulliSinhDivLogCoefficient (k + 1)) =
        ∑ k ∈ range (n + 1),
          ((2 : ℚ) ^ (2 * (k + 1) - 1) *
              (Nat.choose (2 * n + 3) (2 * (k + 1)) : ℚ) *
              bernoulli (2 * (k + 1))) /
            ((2 * n + 3).factorial : ℚ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k hk
    _ = (n + 1 : ℚ) / ((2 * n + 3).factorial : ℚ) := by
      rw [← Finset.sum_div, weightedEvenBernoulliChooseSum]
    _ = (n + 1 : ℚ) * sinhDivCoefficient (n + 1) := by
      simp only [sinhDivCoefficient]
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
      simp only [div_eq_mul_inv, one_mul]

private theorem massSeries_sinhDiv_mul_derivative_bernoulliLog :
    SaddleExpansion.massSeries sinhDivCoefficient *
        d⁄dX ℚ (SaddleExpansion.massSeries bernoulliSinhDivLogCoefficient) =
      d⁄dX ℚ (SaddleExpansion.massSeries sinhDivCoefficient) := by
  ext n
  simp only [PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_derivative, SaddleExpansion.coeff_massSeries]
  rw [← Finset.sum_range_reflect]
  have hsum := sinhDiv_bernoulliLogDerivative_sum n
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
    have hleft : n + 1 - 1 - k = n - k := by omega
    have hright : n - (n + 1 - 1 - k) + 1 = k + 1 := by omega
    have hcancel : n - (n - k) = k := by omega
    rw [hright, hleft]
    rw [hcancel]
    ring
  · ring

/-- The all-order Bernoulli formula for the formal logarithm of
`sinh(√X)/√X`, including the separately normalized zeroth coefficient. -/
theorem sinhDivLogCoefficient_eq_bernoulli (n : ℕ) :
    sinhDivLogCoefficient n = bernoulliSinhDivLogCoefficient n := by
  have hzero : PowerSeries.constantCoeff
      (SaddleExpansion.massSeries bernoulliSinhDivLogCoefficient) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp
  have hcoeff := SaddleExpansion.coeff_eq_logCoeff_of_derivative_mul_eq
    sinhDivCoefficient sinhDivCoefficient_zero
    massSeries_sinhDiv_mul_derivative_bernoulliLog hzero n
  simpa only [SaddleExpansion.coeff_massSeries, sinhDivLogCoefficient] using
    hcoeff.symm

/-- Explicit positive-index form of the one-scale logarithmic coefficient. -/
theorem sinhDivLogCoefficient_eq_bernoulli_formula
    (n : ℕ) (hn : 1 ≤ n) :
    sinhDivLogCoefficient n =
      (2 : ℚ) ^ (2 * n - 1) * bernoulli (2 * n) /
        ((n : ℚ) * ((2 * n).factorial : ℚ)) := by
  have hn0 : n ≠ 0 := by omega
  rw [sinhDivLogCoefficient_eq_bernoulli,
    bernoulliSinhDivLogCoefficient, if_neg hn0]

/-- All positive centered even cumulants have the Bernoulli--Mersenne closed
form predicted by the spectral report. -/
theorem centeredRvachevEvenCumulant_eq_bernoulliMersenne
    (n : ℕ) (hn : 1 ≤ n) :
    centeredRvachevEvenCumulant n = bernoulliMersenneEvenCumulant n := by
  exact centeredRvachevEvenCumulant_eq_bernoulliMersenne_of_sinhDiv
    n hn (sinhDivLogCoefficient_eq_bernoulli n)

/-- Explicit all-positive-order Bernoulli--Mersenne cumulant formula. -/
theorem centeredRvachevEvenCumulant_eq_bernoulliMersenne_formula
    (n : ℕ) (hn : 1 ≤ n) :
    centeredRvachevEvenCumulant n =
      (2 : ℚ) ^ (2 * n - 1) * bernoulli (2 * n) /
        ((n : ℚ) * ((4 : ℚ) ^ n - 1)) := by
  have hn0 : n ≠ 0 := by omega
  rw [centeredRvachevEvenCumulant_eq_bernoulliMersenne n hn,
    bernoulliMersenneEvenCumulant, if_neg hn0]

/-- The Bernoulli--Mersenne centered-moment recurrence, now with no
coefficient-identification premise. -/
theorem moment_bernoulliMersenne_recurrence (N : ℕ) (hN : 1 ≤ N) :
    moment N =
      (∑ r ∈ Icc 1 N,
        (Nat.choose (2 * N) (2 * r) : ℚ) *
          ((2 : ℚ) ^ (2 * r - 1) * bernoulli (2 * r) /
            ((4 : ℚ) ^ r - 1)) * moment (N - r)) / (N : ℚ) := by
  apply moment_bernoulliMersenne_recurrence_of_sinhDivLog N hN
  intro r hr
  exact sinhDivLogCoefficient_eq_bernoulli r

/-- The cumulant recurrence and Proposition 22's reciprocal-sinh recurrence
are two exact finite Bernoulli transforms of the same moment. -/
theorem bernoulliMersenne_recurrence_eq_propositionTwentyTwo
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ r ∈ Icc 1 N,
        (Nat.choose (2 * N) (2 * r) : ℚ) *
          ((2 : ℚ) ^ (2 * r - 1) * bernoulli (2 * r) /
            ((4 : ℚ) ^ r - 1)) * moment (N - r)) / (N : ℚ) =
      (∑ k ∈ Icc 1 N,
        (2 : ℚ) ^ (2 * N - 2 * k) * ((2 : ℚ) ^ (2 * k) - 2) *
          Nat.choose (2 * N) (2 * k) * bernoulli (2 * k) *
            moment (N - k)) /
        ((2 : ℚ) ^ (2 * N) - 1) := by
  calc
    _ = moment N := (moment_bernoulliMersenne_recurrence N hN).symm
    _ = _ := moment_bernoulli_recurrence N hN

end

end Fabius
