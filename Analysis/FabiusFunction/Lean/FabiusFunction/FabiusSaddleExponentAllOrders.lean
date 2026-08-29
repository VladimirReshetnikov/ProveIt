import FabiusFunction.NegativeLaplaceVerticalOrdinaryJets
import FabiusFunction.FabiusSaddlePolynomialCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# All-orders algebra of the centered Fabius saddle exponent

On the dyadic Lambert central arc the saddle data are a phase `t`, a radius
`r = 2^t`, and a Gaussian scale `epsilon` fixed by `t * epsilon^2 = 1`.  Once
the standard Gaussian is factored out of the saddle kernel, the exponent left
over is

`t * epsilon * v * I + v^2/2 + L_r (epsilon * v) - log (1 + epsilon * v * I)`,

with `L_r = negativeLaplaceVerticalLog F r` the branch-safe vertical logarithm
normalized to vanish at the origin.  This module regroups the Taylor
polynomials of those two logarithms into a single power series in `epsilon`
with exactly identified coefficients.  Write `d_n` for the bounded exponent
jet, `f_n` for the flat forward-product jet, and `s_n = (-1)^(n+1) n!` for the
slope of the `(n+1)`st scaled ordinary derivative of the negative-Laplace
logarithm.  The `Complex.logTaylor` counterterm supplies exactly the constant
`s_(k-1)` that promotes the periodic part of the `k`th scaled jet to the
bounded jet `d_(k-1)`, leaving a bounded piece
`I^k (d_(k-1) - f_(k-1)) v^k / k!` beside a piece `t * I^k s_(k-1) v^k / k!`
that is linear in `t`.  Because `t * epsilon^2 = 1`, the linear piece
reappears two `epsilon` orders lower, so the exact coefficient of `epsilon^m`
is the bounded term of order `m` plus the slope term of order `m + 2`.

Isolating that index juggling is the point of the module.
`FabiusSaddleCentralAllOrders` feeds the results below into
`dyadicLambertCenteredExponent_sub_truncation_eq`, the exact decomposition of
the centered exponent into its periodic truncation plus a vertical Taylor
remainder, a `Complex.log` Taylor remainder, two boundary jets, and the flat
forward-product jets; `FabiusSaddleMassAllOrders` bounds those pieces on the
way to the full asymptotic expansion of the saddle-kernel mass.

## Main results

* `negativeLaplaceExactExponentBoundedTerm`, `negativeLaplaceExponentSlopeTerm`
  and `negativeLaplaceExactExponentCoefficient` -- the two graded pieces and
  the exact coefficient of `epsilon^m`, indexed by the power of `epsilon`
  rather than by the jet order, and all zero in order `0`.
* `negativeLaplaceExactExponentCoefficient_eq` -- that coefficient differs from
  the periodic polynomial coefficient `negativeLaplaceExponentCoefficient` of
  `FabiusFunction.FabiusSaddleCoefficientRecurrence` by exactly one flat
  forward-product term.
* `centeredJetSum_eq_exactExponentSum_boundary` -- the reindexing identity: the
  imposed linear phase and the Gaussian quadratic are cancelled by the first
  two slope terms, and the jet sum through order `M + 2` collapses to the
  coefficient sum through order `M` plus two boundary terms.
* `negativeLaplaceVerticalTaylorSum` and
  `verticalTaylorSum_sub_logTaylor_eq_jetSum` -- the order-`K` Taylor sum of
  `L_r` at `theta = epsilon * v`, and the identification of its difference
  with `Complex.logTaylor (K + 1)` as the graded jet sum.

Nothing in this module is an estimate.  The reindexing identity holds for all
complex `epsilon` and `v` obeying `t * epsilon^2 = 1`, with no smallness
hypothesis, and its boundary terms of orders `epsilon^(M+1)` and
`epsilon^(M+2)` are exact summands rather than remainders; they are bounded
downstream.  The variable `t` is the dyadic phase, so the radius is `2^t`, and
consumers instantiate it at `dyadicLambertPhase`.
-/

set_option autoImplicit false

open Complex Filter Set
open scoped BigOperators Topology

namespace Fabius

/-- The bounded part of the exact order-`k` centered exponent jet, including
the (flat) forward-product correction. -/
noncomputable def negativeLaplaceExactExponentBoundedTerm
    (k : ℕ) (t : ℝ) (v : ℂ) : ℂ :=
  match k with
  | 0 => 0
  | n + 1 =>
      Complex.I ^ (n + 1) *
        ((negativeLaplaceBoundedExponentJet n t -
          negativeLaplaceForwardScaledJet n t : ℝ) : ℂ) *
        v ^ (n + 1) / ((n + 1).factorial : ℕ)

/-- The linear-in-`t` part of the exact order-`k` centered exponent jet. -/
noncomputable def negativeLaplaceExponentSlopeTerm
    (k : ℕ) (v : ℂ) : ℂ :=
  match k with
  | 0 => 0
  | n + 1 =>
      Complex.I ^ (n + 1) * (negativeLaplaceJetSlope n : ℂ) *
        v ^ (n + 1) / ((n + 1).factorial : ℕ)

/-- Exact coefficient before discarding the flat forward-product jet. -/
noncomputable def negativeLaplaceExactExponentCoefficient
    (m : ℕ) (t : ℝ) (v : ℂ) : ℂ :=
  match m with
  | 0 => 0
  | n + 1 =>
      negativeLaplaceExactExponentBoundedTerm (n + 1) t v +
        negativeLaplaceExponentSlopeTerm (n + 3) v

/-- The order-zero exact exponent coefficient vanishes. -/
@[simp] theorem negativeLaplaceExactExponentCoefficient_zero
    (t : ℝ) (v : ℂ) :
    negativeLaplaceExactExponentCoefficient 0 t v = 0 := rfl

/-- The exact exponent coefficient differs from the periodic polynomial
coefficient only by the forward-product jet. -/
theorem negativeLaplaceExactExponentCoefficient_eq
    (m : ℕ) (t v : ℝ) :
    negativeLaplaceExactExponentCoefficient m t v =
      negativeLaplaceExponentCoefficient m t v -
        match m with
        | 0 => 0
        | n + 1 =>
            Complex.I ^ (n + 1) *
              (negativeLaplaceForwardScaledJet n t : ℂ) *
              (v : ℂ) ^ (n + 1) / ((n + 1).factorial : ℕ) := by
  cases m with
  | zero => simp [negativeLaplaceExactExponentCoefficient,
      negativeLaplaceExponentCoefficient]
  | succ n =>
      unfold negativeLaplaceExactExponentCoefficient
        negativeLaplaceExactExponentBoundedTerm
        negativeLaplaceExponentSlopeTerm
        negativeLaplaceExponentCoefficient
      push_cast
      ring

/-- The order-zero bounded exponent term vanishes. -/
@[simp] theorem negativeLaplaceExactExponentBoundedTerm_zero
    (t : ℝ) (v : ℂ) :
    negativeLaplaceExactExponentBoundedTerm 0 t v = 0 := rfl

/-- The order-zero exponent slope term vanishes. -/
@[simp] theorem negativeLaplaceExponentSlopeTerm_zero (v : ℂ) :
    negativeLaplaceExponentSlopeTerm 0 v = 0 := rfl

/-- The order-one slope term is `-Complex.I * v`, since the jet slope
`negativeLaplaceJetSlope 0` equals `-1`.  Its only use in the corpus is the
base case of `centeredJetSum_eq_exactExponentSum_boundary`, where it cancels
the imposed linear phase `t * eps * v * I`. -/
lemma negativeLaplaceExponentSlopeTerm_one (v : ℂ) :
    negativeLaplaceExponentSlopeTerm 1 v = -Complex.I * v := by
  simp [negativeLaplaceExponentSlopeTerm, negativeLaplaceJetSlope]

/-- The order-two slope term is `-(v ^ 2) / 2`.  Its only use in the corpus
is the base case of `centeredJetSum_eq_exactExponentSum_boundary`, where
`t * eps ^ 2 = 1` turns it into the cancellation of the Gaussian quadratic
`v ^ 2 / 2`. -/
lemma negativeLaplaceExponentSlopeTerm_two (v : ℂ) :
    negativeLaplaceExponentSlopeTerm 2 v = -(v ^ 2) / 2 := by
  norm_num [negativeLaplaceExponentSlopeTerm, negativeLaplaceJetSlope]

/-- Pure finite-sum reindexing behind the all-orders centered exponent.
The first two slope terms cancel the imposed linear phase and Gaussian
quadratic term; every later slope term shifts down by two powers of
`epsilon` because `t * epsilon^2 = 1`. -/
theorem centeredJetSum_eq_exactExponentSum_boundary
    (M : ℕ) (t : ℝ) (eps v : ℂ)
    (hscale : (t : ℂ) * eps ^ 2 = 1) :
    (t : ℂ) * eps * v * Complex.I + v ^ 2 / 2 +
        ∑ k ∈ Finset.range (M + 3),
          eps ^ k *
            (negativeLaplaceExactExponentBoundedTerm k t v +
              (t : ℂ) * negativeLaplaceExponentSlopeTerm k v) =
      ∑ m ∈ Finset.range (M + 1),
          eps ^ m * negativeLaplaceExactExponentCoefficient m t v +
        eps ^ (M + 1) *
          negativeLaplaceExactExponentBoundedTerm (M + 1) t v +
        eps ^ (M + 2) *
          negativeLaplaceExactExponentBoundedTerm (M + 2) t v := by
  induction M with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        negativeLaplaceExactExponentBoundedTerm_zero,
        negativeLaplaceExponentSlopeTerm_zero,
        negativeLaplaceExactExponentCoefficient_zero, pow_zero, zero_add,
        mul_zero, add_zero]
      rw [negativeLaplaceExponentSlopeTerm_one,
        negativeLaplaceExponentSlopeTerm_two]
      have hquad : (t : ℂ) * eps ^ 2 * v ^ 2 = v ^ 2 := by
        calc
          (t : ℂ) * eps ^ 2 * v ^ 2 = ((t : ℂ) * eps ^ 2) * v ^ 2 := by ring
          _ = v ^ 2 := by rw [hscale, one_mul]
      ring_nf
      rw [hquad]
      ring
  | succ M ih =>
      have hshift : (t : ℂ) * eps ^ (M + 3) = eps ^ (M + 1) := by
        calc
          (t : ℂ) * eps ^ (M + 3) =
              ((t : ℂ) * eps ^ 2) * eps ^ (M + 1) := by
                rw [show M + 3 = 2 + (M + 1) by omega, pow_add]
                ring
          _ = eps ^ (M + 1) := by rw [hscale, one_mul]
      have hleftSum :
          (∑ k ∈ Finset.range (M + 1 + 3),
            eps ^ k *
              (negativeLaplaceExactExponentBoundedTerm k t v +
                (t : ℂ) * negativeLaplaceExponentSlopeTerm k v)) =
          (∑ k ∈ Finset.range (M + 3),
            eps ^ k *
              (negativeLaplaceExactExponentBoundedTerm k t v +
                (t : ℂ) * negativeLaplaceExponentSlopeTerm k v)) +
            eps ^ (M + 3) *
              (negativeLaplaceExactExponentBoundedTerm (M + 3) t v +
                (t : ℂ) * negativeLaplaceExponentSlopeTerm (M + 3) v) := by
        rw [show M + 1 + 3 = (M + 3) + 1 by omega,
          Finset.sum_range_succ]
      rw [hleftSum]
      rw [show (t : ℂ) * eps * v * Complex.I + v ^ 2 / 2 +
          (∑ k ∈ Finset.range (M + 3),
            eps ^ k *
              (negativeLaplaceExactExponentBoundedTerm k t v +
                (t : ℂ) * negativeLaplaceExponentSlopeTerm k v) +
            eps ^ (M + 3) *
              (negativeLaplaceExactExponentBoundedTerm (M + 3) t v +
                (t : ℂ) * negativeLaplaceExponentSlopeTerm (M + 3) v)) =
          ((t : ℂ) * eps * v * Complex.I + v ^ 2 / 2 +
            ∑ k ∈ Finset.range (M + 3),
              eps ^ k *
                (negativeLaplaceExactExponentBoundedTerm k t v +
                  (t : ℂ) * negativeLaplaceExponentSlopeTerm k v)) +
            eps ^ (M + 3) *
              (negativeLaplaceExactExponentBoundedTerm (M + 3) t v +
                (t : ℂ) * negativeLaplaceExponentSlopeTerm (M + 3) v) by ring,
        ih]
      have hrightSum :
          (∑ m ∈ Finset.range (M + 1 + 1),
            eps ^ m * negativeLaplaceExactExponentCoefficient m t v) =
          (∑ m ∈ Finset.range (M + 1),
            eps ^ m * negativeLaplaceExactExponentCoefficient m t v) +
            eps ^ (M + 1) *
              negativeLaplaceExactExponentCoefficient (M + 1) t v := by
        rw [show M + 1 + 1 = (M + 1) + 1 by rfl,
          Finset.sum_range_succ]
      rw [hrightSum]
      have hcoeff : negativeLaplaceExactExponentCoefficient (M + 1) t v =
          negativeLaplaceExactExponentBoundedTerm (M + 1) t v +
            negativeLaplaceExponentSlopeTerm (M + 3) v := by rfl
      rw [hcoeff]
      have hnew : eps ^ (M + 3) *
            (negativeLaplaceExactExponentBoundedTerm (M + 3) t v +
              (t : ℂ) * negativeLaplaceExponentSlopeTerm (M + 3) v) =
          eps ^ (M + 3) *
              negativeLaplaceExactExponentBoundedTerm (M + 3) t v +
            eps ^ (M + 1) *
              negativeLaplaceExponentSlopeTerm (M + 3) v := by
        calc
          _ = eps ^ (M + 3) *
                negativeLaplaceExactExponentBoundedTerm (M + 3) t v +
              ((t : ℂ) * eps ^ (M + 3)) *
                negativeLaplaceExponentSlopeTerm (M + 3) v := by ring
          _ = _ := by rw [hshift]
      rw [hnew]
      ring

/-- Taylor sum of the branch-safe vertical logarithm at the dyadic radius
`r = 2^t`, evaluated at `theta = epsilon * v`. -/
noncomputable def negativeLaplaceVerticalTaylorSum
    (F : BoundedFabius) (K : ℕ) (t eps v : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (K + 1),
    ((((eps * v) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
      iteratedDeriv k
        (negativeLaplaceVerticalLog F ((2 : ℝ) ^ t)) 0)

/-- The vertical Taylor sum and denominator-log Taylor sum combine
coefficientwise into the bounded and slope jets used above. -/
theorem verticalTaylorSum_sub_logTaylor_eq_jetSum
    (F : BoundedFabius) (hF : IsFabius F)
    (K : ℕ) (t eps v : ℝ) :
    negativeLaplaceVerticalTaylorSum F K t eps v -
        Complex.logTaylor (K + 1)
          (((eps * v : ℝ) : ℂ) * Complex.I) =
      ∑ k ∈ Finset.range (K + 1),
        (eps : ℂ) ^ k *
          (negativeLaplaceExactExponentBoundedTerm k t v +
            (t : ℂ) * negativeLaplaceExponentSlopeTerm k v) := by
  unfold negativeLaplaceVerticalTaylorSum Complex.logTaylor
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  cases k with
  | zero =>
      simp [negativeLaplaceVerticalLog_zero]
  | succ n =>
      rw [iteratedDeriv_negativeLaplaceVerticalLog_at_zero_eq_ordinary
        F hF n (Real.rpow_pos_of_pos (by norm_num) t)]
      rw [iteratedDeriv_negativeLaplaceLog_eq_ordinaryDeriv
        (n + 1) (Real.rpow_pos_of_pos (by norm_num) t)]
      rw [show negativeLaplaceLogOrdinaryDeriv (n + 1) ((2 : ℝ) ^ t) =
          iteratedDeriv (n + 1) negativeLaplaceLog ((2 : ℝ) ^ t) by
        symm
        exact iteratedDeriv_negativeLaplaceLog_eq_ordinaryDeriv
          (n + 1) (Real.rpow_pos_of_pos (by norm_num) t)]
      have hscaled := negativeLaplaceScaledOrdinaryJet_eq n t
      unfold negativeLaplaceScaledOrdinaryJet at hscaled
      have hscaledC := congrArg (fun y : ℝ => (y : ℂ)) hscaled
      have hchain :
          (((((2 : ℝ) ^ t : ℝ) : ℂ) * Complex.I) ^ (n + 1) *
            ((iteratedDeriv (𝕜 := ℝ) (n + 1) negativeLaplaceLog
              ((2 : ℝ) ^ t) : ℝ) : ℂ)) =
          Complex.I ^ (n + 1) *
            ((((2 : ℝ) ^ t) ^ (n + 1) *
              iteratedDeriv (n + 1) negativeLaplaceLog ((2 : ℝ) ^ t) : ℝ) : ℂ) := by
        rw [mul_pow]
        push_cast
        ring
      rw [hchain, hscaledC]
      simp only [negativeLaplaceExactExponentBoundedTerm,
        negativeLaplaceExponentSlopeTerm]
      unfold negativeLaplaceBoundedExponentJet negativeLaplaceJetSlope
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      push_cast
      have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hfac]
      ring

end Fabius
