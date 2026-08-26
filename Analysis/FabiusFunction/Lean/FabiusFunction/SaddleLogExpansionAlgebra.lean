import FabiusFunction.SaddleExpansionAlgebra

/-!
# Logarithmic coefficient algebra for saddle expansions

Given a formal series with unit constant term,

`A(u) = 1 + a_1 u + a_2 u^2 + ...`,

this module builds the coefficient sequence of `log A` directly, as the
coefficient form of `B' A = A'` divided through by `n + 1` and solved for
`b_{n+1}`:

`b_0 = 0`,  `b_{n+1} = a_{n+1} - (n+1)⁻¹ * ∑ j < n, (n - j) * b_{n-j} * a_{j+1}`.

Everything here is finite ring arithmetic with a single rational scalar, so
the recurrence lives in an arbitrary commutative `ℚ`-algebra `R`; the corpus
instantiates `R` at `ℝ`, `Polynomial ℝ`, `C(ℝ, ℝ)`, and function types
`α → ℝ`.  That is why the module exists.  `PowerSeries.logOf` is defined by
substitution into a universal series, which is awkward to unfold, to
evaluate, or to bound coefficientwise, whereas `logCoeff` reduces to a sum of
`n` explicit terms that downstream files can rewrite and estimate.  Nothing
is lost by preferring the recurrence, because
`FabiusFunction.SaddleLogExpansionPowerSeries` feeds the uniqueness theorem
below into a proof that `logSeries a = PowerSeries.logOf (massSeries a)`.

This is the logarithmic twin of the `expCoeff` layer of
`FabiusFunction.SaddleExpansionAlgebra`, and it carries the same structural
toolkit.  Its consumers are `FabiusFunction.SaddleLogAsymptoticTransfer`
(logarithms of full Poincare expansions),
`FabiusFunction.FabiusSaddleExpansionCoefficients` (the real, continuous,
bounded logarithmic coefficients of the Fabius saddle expansion), and
`FabiusFunction.FabiusLambertFormalLog` together with
`FabiusFunction.FabiusLambertAllOrderRemainder` (the all-order dyadic
Lambert displacement coefficients).

## Main results

* `logCoeff` -- the recurrence itself, with `logCoeff_zero`, `logCoeff_succ`,
  `logCoeff_one`, and `logCoeff_two` as its unfolding lemmas.
* `massSeries`, `logSeries` -- the input and output coefficient sequences
  packaged as `PowerSeries R`, with the expected `coeff` simp lemmas.
* `massSeries_mul_derivative_logSeries` -- correctness: when `a 0 = 1` the
  generated series satisfies `A * B' = A'`, for `A = massSeries a` and
  `B = logSeries a`.  `derivative_logSeries_mul_massSeries` is the commuted
  form.
* `coeff_eq_logCoeff_of_derivative_mul_eq` and `logSeries_unique` -- the
  converse, by strong induction on the coefficient index: `logSeries a` is
  the only solution of `A * B' = A'` with vanishing constant term.
* `expSeries_logCoeff` and `logSeries_expCoeff` -- the logarithmic and
  exponential recurrences are inverse coefficient transforms after imposing
  the necessary unit-constant and zero-constant normalizations.  The
  positive-index forms `expCoeff_logCoeff_of_pos` and
  `logCoeff_expCoeff_of_pos` need no normalization at all, while the
  `..._eq_ite` forms state the exact all-index normalization.
* `logCoeff_congr_of_pos`, `logCoeff_eq_of_forall_pos` -- coefficient `n`
  depends only on the positive input coefficients through order `n`, and
  agreement at every positive index gives equality of the whole generated
  family; `logCoeff_congr` is the convenient unrestricted-index wrapper.
  This is what lets a truncated mass polynomial stand in for the full series.
* `map_logCoeff`, `logCoeff_rescale`, `logCoeff_apply`, `logCoeff_parity` --
  the recurrence commutes with `ℚ`-algebra morphisms, converts the rescaling
  `fun j => c ^ j * a j` into multiplication by `c ^ n`, commutes with
  evaluation of function-valued coefficients at a point, and preserves parity
  of the coefficients in a parameter.

Conventions.  `logCoeff a` is defined for every `a` but never reads `a 0`.
The differential-equation and normalized inverse statements therefore assume
`a 0 = 1`; the positive-index and explicit `ite` forms instead state exactly
what happens without that hypothesis.  Fixing `b_0 = 0` selects the branch of
the logarithm with vanishing constant term.  The rational scalar `(n+1)⁻¹` is
the only reason `Algebra ℚ R` is assumed throughout; no topology, order, or
norm is used anywhere in this module.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius.SaddleExpansion

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Coefficients of the formal logarithm of a series with constant term one.
The zeroth input coefficient is intentionally absent from the recurrence; the
correctness theorem assumes that it is one. -/
def logCoeff (a : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 =>
      a (n + 1) - ((n + 1 : ℚ)⁻¹) •
        (∑ j ∈ range n,
          ((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1))
termination_by n => n
decreasing_by omega

/-- The logarithmic recurrence is normalized by `logCoeff a 0 = 0`. -/
@[simp] theorem logCoeff_zero (a : ℕ → R) : logCoeff a 0 = 0 := by
  rw [logCoeff]

/-- At positive order the logarithmic coefficients obey
`logCoeff a (n + 1) = a (n + 1) - (n + 1)⁻¹ •
  ∑ j < n, (n - j) * logCoeff a (n - j) * a (j + 1)`. -/
theorem logCoeff_succ (a : ℕ → R) (n : ℕ) :
    logCoeff a (n + 1) =
      a (n + 1) - ((n + 1 : ℚ)⁻¹) •
        (∑ j ∈ range n,
          ((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1)) := by
  rw [logCoeff]

/-- The first logarithmic coefficient is `a 1`. -/
@[simp] theorem logCoeff_one (a : ℕ → R) :
    logCoeff a 1 = a 1 := by
  rw [show 1 = 0 + 1 by omega, logCoeff_succ]
  simp

/-- The second logarithmic coefficient is
`a 2 - (2 : ℚ)⁻¹ • (a 1 * a 1)`. -/
theorem logCoeff_two (a : ℕ → R) :
    logCoeff a 2 = a 2 - ((2 : ℚ)⁻¹) • (a 1 * a 1) := by
  rw [show 2 = 1 + 1 by omega, logCoeff_succ]
  simp
  norm_num

/-- The input mass series. -/
def massSeries (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk a

/-- The formal logarithmic series generated by `logCoeff`. -/
def logSeries (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (logCoeff a)

omit [Algebra ℚ R] in
/-- The coefficient of `Xⁿ` in `massSeries a` is exactly `a n`. -/
@[simp] theorem coeff_massSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (massSeries a) = a n := by
  rw [massSeries, PowerSeries.coeff_mk]

/-- The coefficient of `Xⁿ` in `logSeries a` is `logCoeff a n`. -/
@[simp] theorem coeff_logSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (logSeries a) = logCoeff a n := by
  rw [logSeries, PowerSeries.coeff_mk]

/-- The generated logarithmic series has constant coefficient zero. -/
@[simp] theorem constantCoeff_logSeries (a : ℕ → R) :
    PowerSeries.constantCoeff (logSeries a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

/-- Formal correctness of the logarithmic recurrence: if `A(0)=1`, then
the generated series `B` satisfies `B' A = A'`. -/
theorem massSeries_mul_derivative_logSeries (a : ℕ → R)
    (ha0 : a 0 = 1) :
    massSeries a * d⁄dX R (logSeries a) = d⁄dX R (massSeries a) := by
  ext n
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_derivative, coeff_massSeries]
  simp_rw [PowerSeries.coeff_derivative, coeff_logSeries, coeff_massSeries]
  rw [sum_range_succ']
  simp only [Nat.sub_zero]
  rw [ha0, one_mul]
  have hshift :
      ∑ k ∈ range n,
          a (k + 1) *
            (logCoeff a (n - (k + 1) + 1) *
              (((n - (k + 1) : ℕ) : R) + 1)) =
        ∑ k ∈ range n,
          ((n - k : ℕ) : R) * logCoeff a (n - k) * a (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := mem_range.1 hk
    have hindex : n - (k + 1) + 1 = n - k := by omega
    have hcast : (((n - (k + 1) : ℕ) : R) + 1) =
        ((n - k : ℕ) : R) := by
      rw [← hindex, Nat.cast_add, Nat.cast_one]
    rw [hindex, hcast]
    ring
  rw [hshift, logCoeff_succ]
  simp only [Algebra.smul_def]
  let q : R := algebraMap ℚ R (n + 1 : ℚ)
  let qi : R := algebraMap ℚ R ((n + 1 : ℚ)⁻¹)
  let S : R := ∑ k ∈ range n,
    ((n - k : ℕ) : R) * logCoeff a (n - k) * a (k + 1)
  have hqi : qi * q = 1 := by
    dsimp [qi, q]
    rw [← map_mul, inv_mul_cancel₀]
    · rw [map_one]
    · exact_mod_cast Nat.succ_ne_zero n
  have hcancel : qi * S * q = S := by
    calc
      qi * S * q = qi * q * S := by ring
      _ = S := by rw [hqi, one_mul]
  have hqcast : (n + 1 : R) = q := by
    dsimp [q]
    norm_num
  rw [hqcast]
  change S + (a (n + 1) - qi * S) * q = a (n + 1) * q
  rw [sub_mul, hcancel]
  ring

/-- Commuted correctness identity: if `a 0 = 1`, then the generated series
satisfy `(logSeries a)' * massSeries a = (massSeries a)'`. -/
theorem derivative_logSeries_mul_massSeries (a : ℕ → R)
    (ha0 : a 0 = 1) :
    d⁄dX R (logSeries a) * massSeries a = d⁄dX R (massSeries a) := by
  rw [mul_comm]
  exact massSeries_mul_derivative_logSeries a ha0

/-- The logarithmic recurrence is the unique zero-constant solution of
`B' A = A'` for a unit-constant mass series `A`. -/
theorem coeff_eq_logCoeff_of_derivative_mul_eq
    (a : ℕ → R) (ha0 : a 0 = 1) {B : PowerSeries R}
    (hderiv : massSeries a * d⁄dX R B = d⁄dX R (massSeries a))
    (hzero : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    PowerSeries.coeff n B = logCoeff a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
            logCoeff_zero] using hzero
      | succ n =>
          have hcoeff := congrArg (PowerSeries.coeff n) hderiv
          rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
            PowerSeries.coeff_derivative, coeff_massSeries] at hcoeff
          simp_rw [PowerSeries.coeff_derivative, coeff_massSeries] at hcoeff
          rw [sum_range_succ'] at hcoeff
          simp only [Nat.sub_zero] at hcoeff
          rw [ha0, one_mul] at hcoeff
          have hshift :
              ∑ k ∈ range n,
                  a (k + 1) *
                    (PowerSeries.coeff (n - (k + 1) + 1) B *
                      (((n - (k + 1) : ℕ) : R) + 1)) =
                ∑ k ∈ range n,
                  a (k + 1) * ((n - k : ℕ) : R) *
                    PowerSeries.coeff (n - k) B := by
            apply Finset.sum_congr rfl
            intro k hk
            have hklt : k < n := mem_range.1 hk
            have hindex : n - (k + 1) + 1 = n - k := by omega
            have hcast : (((n - (k + 1) : ℕ) : R) + 1) =
                ((n - k : ℕ) : R) := by
              rw [← hindex, Nat.cast_add, Nat.cast_one]
            rw [hindex, hcast]
            ring
          rw [hshift] at hcoeff
          have hsum :
              ∑ j ∈ range n,
                  a (j + 1) * ((n - j : ℕ) : R) *
                    PowerSeries.coeff (n - j) B =
                ∑ j ∈ range n,
                  ((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ih (n - j) (by omega)]
            ring
          rw [hsum] at hcoeff
          rw [logCoeff_succ]
          simp only [Algebra.smul_def]
          let q : R := algebraMap ℚ R (n + 1 : ℚ)
          let qi : R := algebraMap ℚ R ((n + 1 : ℚ)⁻¹)
          let S : R := ∑ j ∈ range n,
            ((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1)
          have hqi : qi * q = 1 := by
            dsimp [qi, q]
            rw [← map_mul, inv_mul_cancel₀]
            · rw [map_one]
            · exact_mod_cast Nat.succ_ne_zero n
          have hqcast : (n + 1 : R) = q := by
            dsimp [q]
            norm_num
          rw [hqcast] at hcoeff
          change S + PowerSeries.coeff (n + 1) B * q =
            a (n + 1) * q at hcoeff
          have hprod : PowerSeries.coeff (n + 1) B * q =
              a (n + 1) * q - S := by
            rw [← hcoeff]
            ring
          change PowerSeries.coeff (n + 1) B = a (n + 1) - qi * S
          calc
            PowerSeries.coeff (n + 1) B =
                qi * (PowerSeries.coeff (n + 1) B * q) := by
              symm
              calc
                qi * (PowerSeries.coeff (n + 1) B * q) =
                    qi * q * PowerSeries.coeff (n + 1) B := by ring
                _ = PowerSeries.coeff (n + 1) B := by rw [hqi, one_mul]
            _ = qi * (a (n + 1) * q - S) := by rw [hprod]
            _ = a (n + 1) - qi * S := by
              have hqa : qi * (a (n + 1) * q) = a (n + 1) := by
                calc
                  qi * (a (n + 1) * q) = qi * q * a (n + 1) := by ring
                  _ = a (n + 1) := by rw [hqi, one_mul]
              rw [mul_sub, hqa]

/-- If `a 0 = 1`, a zero-constant series satisfying
`massSeries a * B' = (massSeries a)'` is the generated logarithmic series. -/
theorem logSeries_unique (a : ℕ → R) (ha0 : a 0 = 1)
    {B : PowerSeries R}
    (hderiv : massSeries a * d⁄dX R B = d⁄dX R (massSeries a))
    (hzero : PowerSeries.constantCoeff B = 0) :
    B = logSeries a := by
  ext n
  rw [coeff_logSeries]
  exact coeff_eq_logCoeff_of_derivative_mul_eq a ha0 hderiv hzero n

/-- Exponentiating the recursive logarithm recovers a unit-constant input
series.  The hypothesis at index zero is necessary: every `expSeries` has
constant coefficient one, while `logCoeff` intentionally ignores `a 0`. -/
theorem expSeries_logCoeff (a : ℕ → R) (ha0 : a 0 = 1) :
    expSeries (logCoeff a) = massSeries a := by
  symm
  apply expSeries_unique (logCoeff a)
  · simpa only [exponentSeries, logSeries] using
      (derivative_logSeries_mul_massSeries a ha0).symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_massSeries, ha0]

/-- Coefficientwise form of `expSeries_logCoeff`, valid at every index,
including index zero. -/
theorem expCoeff_logCoeff (a : ℕ → R) (ha0 : a 0 = 1) (n : ℕ) :
    expCoeff (logCoeff a) n = a n := by
  have h := congrArg (PowerSeries.coeff n) (expSeries_logCoeff a ha0)
  simpa only [coeff_expSeries, coeff_massSeries] using h

/-- Taking the recursive logarithm of the exponential recurrence recovers a
zero-constant exponent series.  The zero-constant hypothesis is exactly what
is needed at index zero, since `expCoeff` does not depend on `E 0`. -/
theorem logSeries_expCoeff (E : ℕ → R) (hEzero : E 0 = 0) :
    logSeries (expCoeff E) = exponentSeries E := by
  symm
  apply logSeries_unique (expCoeff E) (by simp)
  · change expSeries E * d⁄dX R (exponentSeries E) =
      d⁄dX R (expSeries E)
    rw [derivative_expSeries]
    exact mul_comm _ _
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_exponentSeries, hEzero]

/-- Coefficientwise form of `logSeries_expCoeff`, valid at every index,
including index zero. -/
theorem logCoeff_expCoeff (E : ℕ → R) (hEzero : E 0 = 0) (n : ℕ) :
    logCoeff (expCoeff E) n = E n := by
  have h := congrArg (PowerSeries.coeff n) (logSeries_expCoeff E hEzero)
  simpa only [coeff_logSeries, coeff_exponentSeries] using h

/-- The coefficient of order `n` depends only on positive input coefficients
through order `n`; the zeroth input coefficient is irrelevant. -/
theorem logCoeff_congr_of_pos {a b : ℕ → R} (n : ℕ)
    (hab : ∀ j, 0 < j → j ≤ n → a j = b j) :
    logCoeff a n = logCoeff b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [logCoeff_succ, logCoeff_succ,
            hab (n + 1) (by omega) le_rfl]
          congr 1
          apply congrArg (fun z => ((n + 1 : ℚ)⁻¹) • z)
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := mem_range.1 hj
          rw [ih (n - j) (by omega)]
          · rw [hab (j + 1) (by omega) (by omega)]
          · intro k hkpos hk
            exact hab k hkpos (by omega)

/-- Input families agreeing at every positive index generate the same
logarithmic-coefficient family; index zero is ignored. -/
theorem logCoeff_eq_of_forall_pos {a b : ℕ → R}
    (hab : ∀ j, 0 < j → a j = b j) :
    logCoeff a = logCoeff b := by
  funext n
  apply logCoeff_congr_of_pos n
  intro j hj _hjle
  exact hab j hj

/-- The coefficient of order `n` depends only on input coefficients through
order `n`.  This compatibility wrapper retains the original API; use
`logCoeff_congr_of_pos` when the inputs may differ at index zero. -/
theorem logCoeff_congr {a b : ℕ → R} (n : ℕ)
    (hab : ∀ j ≤ n, a j = b j) :
    logCoeff a n = logCoeff b n := by
  apply logCoeff_congr_of_pos n
  intro j _hjpos hj
  exact hab j hj

/-- At every positive index, exponentiating the recursive logarithm recovers
the input coefficient without any assumption on its zeroth coefficient. -/
theorem expCoeff_logCoeff_of_pos (a : ℕ → R) (n : ℕ) (hn : 0 < n) :
    expCoeff (logCoeff a) n = a n := by
  let a' : ℕ → R := fun j => if j = 0 then 1 else a j
  have ha'0 : a' 0 = 1 := by simp [a']
  have hlog : logCoeff a = logCoeff a' := by
    apply logCoeff_eq_of_forall_pos
    intro j hj
    simp [a', Nat.ne_of_gt hj]
  calc
    expCoeff (logCoeff a) n = expCoeff (logCoeff a') n := by rw [hlog]
    _ = a' n := expCoeff_logCoeff a' ha'0 n
    _ = a n := by simp [a', Nat.ne_of_gt hn]

/-- At every positive index, taking the recursive logarithm of the exponential
recurrence recovers the exponent coefficient without assuming it vanishes at
index zero. -/
theorem logCoeff_expCoeff_of_pos (E : ℕ → R) (n : ℕ) (hn : 0 < n) :
    logCoeff (expCoeff E) n = E n := by
  let E' : ℕ → R := fun j => if j = 0 then 0 else E j
  have hE'zero : E' 0 = 0 := by simp [E']
  have hexp : expCoeff E = expCoeff E' := by
    apply expCoeff_eq_of_forall_pos
    intro k hkpos
    simp [E', Nat.ne_of_gt hkpos]
  calc
    logCoeff (expCoeff E) n = logCoeff (expCoeff E') n := by rw [hexp]
    _ = E' n := logCoeff_expCoeff E' hE'zero n
    _ = E n := by simp [E', Nat.ne_of_gt hn]

/-- Unconditional all-index form of `expCoeff_logCoeff_of_pos`. At index zero
the exponential recurrence has its fixed normalization `1`; every positive
coefficient recovers the input, independently of `a 0`. -/
theorem expCoeff_logCoeff_eq_ite (a : ℕ → R) (n : ℕ) :
    expCoeff (logCoeff a) n = if n = 0 then 1 else a n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    exact expCoeff_logCoeff_of_pos a n (Nat.pos_of_ne_zero hn)

/-- Unconditional all-index form of `logCoeff_expCoeff_of_pos`. At index zero
the logarithmic recurrence has its fixed normalization `0`; every positive
coefficient recovers the input, independently of `E 0`. -/
theorem logCoeff_expCoeff_eq_ite (E : ℕ → R) (n : ℕ) :
    logCoeff (expCoeff E) n = if n = 0 then 0 else E n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    exact logCoeff_expCoeff_of_pos E n (Nat.pos_of_ne_zero hn)

/-- Formation of logarithmic coefficients commutes with morphisms of
commutative rational algebras. -/
theorem map_logCoeff {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (a : ℕ → R) (n : ℕ) :
    f (logCoeff a n) = logCoeff (fun j => f (a j)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [logCoeff_succ, logCoeff_succ, map_sub, map_smul, map_sum]
          congr 1
          apply congrArg (fun z => ((n + 1 : ℚ)⁻¹) • z)
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := mem_range.1 hj
          simp only [map_mul]
          rw [ih (n - j) (by omega)]
          norm_num

/-- Rescaling the formal parameter by `c` multiplies the logarithmic
coefficient of order `n` by `c^n`. -/
theorem logCoeff_rescale (c : R) (a : ℕ → R) (n : ℕ) :
    logCoeff (fun j => c ^ j * a j) n = c ^ n * logCoeff a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [logCoeff_succ, logCoeff_succ]
          have hsum :
              ∑ j ∈ range n,
                  ((n - j : ℕ) : R) * logCoeff (fun k => c ^ k * a k) (n - j) *
                    (c ^ (j + 1) * a (j + 1)) =
                c ^ (n + 1) *
                  ∑ j ∈ range n,
                    ((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1) := by
            rw [mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : j < n := mem_range.1 hj
            rw [ih (n - j) (by omega)]
            have hdegree : n - j + (j + 1) = n + 1 := by omega
            calc
              ((n - j : ℕ) : R) * (c ^ (n - j) * logCoeff a (n - j)) *
                    (c ^ (j + 1) * a (j + 1)) =
                  (c ^ (n - j) * c ^ (j + 1)) *
                    (((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1)) := by
                      ring
              _ = c ^ (n + 1) *
                    (((n - j : ℕ) : R) * logCoeff a (n - j) * a (j + 1)) := by
                      rw [← pow_add, hdegree]
          rw [hsum]
          simp only [Algebra.smul_def]
          ring

/-- Evaluation of function-valued coefficients commutes with the recursive
logarithmic coefficient engine. -/
theorem logCoeff_apply {V : Type*} (a : ℕ → V → R) (n : ℕ) (v : V) :
    logCoeff a n v = logCoeff (fun j => a j v) n := by
  simpa using map_logCoeff
    (R := V → R) (S := R) (Pi.evalAlgHom ℚ (fun _ : V => R) v) a n

/-- Parameter parity is preserved by the logarithmic coefficient engine. -/
theorem logCoeff_parity {V : Type*} [Neg V] (a : ℕ → V → R)
    (ha : ∀ n v, a n (-v) = (-1 : R) ^ n * a n v)
    (n : ℕ) (v : V) :
    logCoeff a n (-v) = (-1 : R) ^ n * logCoeff a n v := by
  rw [logCoeff_apply, logCoeff_apply]
  rw [logCoeff_congr (R := R) n
    (a := fun j => a j (-v))
    (b := fun j => (-1 : R) ^ j * a j v)]
  · exact logCoeff_rescale (-1 : R) (fun j => a j v) n
  · intro j _hj
    exact ha j v

end

end Fabius.SaddleExpansion
