import FabiusFunction.SaddleExpansionAlgebra
import FabiusFunction.ExponentialBell
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Polynomial.Basic

/-!
# Universal endpoint-transfer polynomials

The endpoint-transfer expansion in the frontier reports begins with the
formal identity

`exp (-∑ j ≥ 2, z^j t^(j-1) / j) = ∑ r ≥ 0, P_r(z) t^r`.

This module isolates its finite algebra from the later probability and
remainder estimates.  The coefficient of `t^r` in the exponent is zero at
`r = 0` and is `-z^(r+1)/(r+1)` for `r > 0`.  Feeding those polynomial
coefficients to the general exponential engine in `SaddleExpansionAlgebra`
defines `endpointTransferPolynomial r` over `ℚ`.

The weighted-partition formula for exponential coefficients supplies a
second, finite description of every `endpointTransferPolynomial r`.  Thus
the recursive, formal-series, and unordered-partition views are connected
without adding analytic assumptions.

The construction is universal: `ℚ[X]` is the free rational algebra on one
generator, and evaluating its generator at an element `z` of any commutative
rational algebra carries both the correction coefficients and their complete
formal series to the coefficients constructed directly in that algebra.
Thus the same finite objects apply to real or complex endpoint moments,
formal polynomial variables, and future parameterized coefficient rings.

No analytic use of `(1 - z t)^(1/t)` is made here.  The theorems below prove
the exact formal exponential identity, with no convergence, branch, moment,
or remainder hypotheses.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial

namespace Fabius

noncomputable section

/-! ## Universal exponent and correction coefficients -/

/-- The coefficient of `t^r` in
`-∑_{j≥2} X^j t^(j-1) / j`, as a polynomial in `X`.

At positive index `r = n + 1` this is `-X^(n+2)/(n+2)`; the constant
coefficient is zero so that formal exponential substitution is defined. -/
def endpointTransferExponentCoefficient : ℕ → ℚ[X]
  | 0 => 0
  | n + 1 => C (-(n + 2 : ℚ)⁻¹) * X ^ (n + 2)

/-- The universal endpoint-transfer polynomial `P_r`.  It is the `r`-th
coefficient of the formal exponential whose exponent coefficients are
`endpointTransferExponentCoefficient`. -/
def endpointTransferPolynomial (r : ℕ) : ℚ[X] :=
  SaddleExpansion.expCoeff endpointTransferExponentCoefficient r

/-- The exponent used by the endpoint-transfer formal series has zero
constant coefficient. -/
@[simp] theorem endpointTransferExponentCoefficient_zero :
    endpointTransferExponentCoefficient 0 = 0 := by
  rfl

/-- Positive exponent coefficients have the literal frontier-report form
`-X^(n+2)/(n+2)`. -/
@[simp] theorem endpointTransferExponentCoefficient_succ (n : ℕ) :
    endpointTransferExponentCoefficient (n + 1) =
      C (-(n + 2 : ℚ)⁻¹) * X ^ (n + 2) := by
  rfl

/-- The correction polynomials obey the universal exponential recurrence.
This finite formula computes `P_(n+1)` entirely from the preceding
polynomials and the exponent monomials through order `n+1`. -/
theorem endpointTransferPolynomial_succ (n : ℕ) :
    endpointTransferPolynomial (n + 1) =
      ((n + 1 : ℚ)⁻¹) •
        (∑ j ∈ range (n + 1),
          (j + 1 : ℚ[X]) *
            (C (-(j + 2 : ℚ)⁻¹) * X ^ (j + 2)) *
              endpointTransferPolynomial (n - j)) := by
  simpa only [endpointTransferPolynomial,
    endpointTransferExponentCoefficient_succ] using
    (SaddleExpansion.expCoeff_succ endpointTransferExponentCoefficient n)

/-- The universal endpoint-transfer polynomial is the finite weighted sum
over partitions of its order, with exponent weights
`endpointTransferExponentCoefficient`. -/
theorem endpointTransferPolynomial_eq_partitionExpSum (r : ℕ) :
    endpointTransferPolynomial r =
      partitionExpSum endpointTransferExponentCoefficient r := by
  simpa only [endpointTransferPolynomial] using
    (congrFun
      (partitionExpSum_eq_expCoeff endpointTransferExponentCoefficient)
      r).symm

/-! ## Exact formal generating identity -/

/-- The power series whose coefficient of `t^r` is the universal polynomial
`P_r`. -/
def endpointTransferSeries : PowerSeries ℚ[X] :=
  SaddleExpansion.expSeries endpointTransferExponentCoefficient

/-- Coefficient extraction from `endpointTransferSeries` returns the
corresponding universal correction polynomial. -/
@[simp] theorem coeff_endpointTransferSeries (r : ℕ) :
    PowerSeries.coeff r endpointTransferSeries =
      endpointTransferPolynomial r := by
  simp [endpointTransferSeries, endpointTransferPolynomial]

/-- **Exact formal endpoint-transfer identity.**  The correction series is
the universal formal exponential evaluated at

`-X² t/2 - X³ t²/3 - X⁴ t³/4 - ⋯`.

This is the formal, assumption-free content of
`exp X * (1 - X t)^(1/t)` in the frontier report. -/
theorem endpointTransferSeries_eq_exp_subst :
    endpointTransferSeries =
      (PowerSeries.exp ℚ[X]).subst
        (SaddleExpansion.exponentSeries
          endpointTransferExponentCoefficient) := by
  exact SaddleExpansion.expSeries_eq_exp_subst
    endpointTransferExponentCoefficient
    endpointTransferExponentCoefficient_zero

/-- Finite truncation of the exact generating identity.  It packages the
first `N` correction polynomials as an ordinary polynomial in the expansion
parameter `t`, with coefficients in `ℚ[X]`. -/
theorem trunc_endpointTransferSeries_eq_sum (N : ℕ) :
    PowerSeries.trunc N endpointTransferSeries =
      ∑ r ∈ range N, Polynomial.monomial r
        (endpointTransferPolynomial r) := by
  rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]
  simp only [coeff_endpointTransferSeries]

/-- Backward-compatible short name for the finite endpoint-transfer
truncation identity. -/
theorem trunc_endpointTransferSeries (N : ℕ) :
    PowerSeries.trunc N endpointTransferSeries =
      ∑ r ∈ range N, Polynomial.monomial r
        (endpointTransferPolynomial r) :=
  trunc_endpointTransferSeries_eq_sum N

/-! ## Universality under evaluation -/

/-- Evaluate a universal endpoint exponent coefficient at `z`.  This
definition uses only the universal property of `ℚ[X]` and therefore makes
sense in every rational algebra. -/
def endpointTransferExponentCoefficientAt
    {R : Type*} [Semiring R] [Algebra ℚ R]
    (z : R) (r : ℕ) : R :=
  Polynomial.aeval z (endpointTransferExponentCoefficient r)

/-- Concise compatibility alias for scalar endpoint exponent coefficients. -/
abbrev endpointTransferExponentAt
    {R : Type*} [Semiring R] [Algebra ℚ R] (z : R) : ℕ → R :=
  endpointTransferExponentCoefficientAt z

/-- Evaluation at any scalar preserves the zero constant exponent
coefficient. -/
@[simp] theorem endpointTransferExponentCoefficientAt_zero
    {R : Type*} [Semiring R] [Algebra ℚ R] (z : R) :
    endpointTransferExponentCoefficientAt z 0 = 0 := by
  simp [endpointTransferExponentCoefficientAt]

/-- Positive scalar exponent coefficients have the expected literal form. -/
@[simp] theorem endpointTransferExponentCoefficientAt_succ
    {R : Type*} [Semiring R] [Algebra ℚ R] (z : R) (n : ℕ) :
    endpointTransferExponentCoefficientAt z (n + 1) =
      algebraMap ℚ R (-(n + 2 : ℚ)⁻¹) * z ^ (n + 2) := by
  simp only [endpointTransferExponentCoefficientAt,
    endpointTransferExponentCoefficient_succ, map_mul,
    Polynomial.aeval_C, Polynomial.aeval_X_pow]

/-- **Universal coefficient-evaluation theorem.**  Evaluating `P_r` at `z`
in any commutative rational algebra is exactly the `r`-th exponential
coefficient formed directly from the scalar exponent
`-z²t/2 - z³t²/3 - ⋯`. -/
theorem aeval_endpointTransferPolynomial
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (z : R) (r : ℕ) :
    Polynomial.aeval z (endpointTransferPolynomial r) =
      SaddleExpansion.expCoeff
        (endpointTransferExponentCoefficientAt z) r := by
  change Polynomial.aeval z
      (SaddleExpansion.expCoeff endpointTransferExponentCoefficient r) =
    SaddleExpansion.expCoeff
      (fun j => Polynomial.aeval z
        (endpointTransferExponentCoefficient j)) r
  exact SaddleExpansion.map_expCoeff (Polynomial.aeval z)
    endpointTransferExponentCoefficient r

/-- **Universal series-evaluation theorem.**  Evaluation of the polynomial
coefficients commutes with formation of the complete endpoint-transfer
series, not merely with each separately stated finite coefficient. -/
theorem map_endpointTransferSeries
    {R : Type*} [CommRing R] [Algebra ℚ R] (z : R) :
    PowerSeries.map (Polynomial.aeval z).toRingHom
        endpointTransferSeries =
      SaddleExpansion.expSeries
        (endpointTransferExponentCoefficientAt z) := by
  change PowerSeries.map (Polynomial.aeval z).toRingHom
      (SaddleExpansion.expSeries endpointTransferExponentCoefficient) =
    SaddleExpansion.expSeries
      (fun r => Polynomial.aeval z
        (endpointTransferExponentCoefficient r))
  exact SaddleExpansion.map_expSeries (Polynomial.aeval z)
    endpointTransferExponentCoefficient

/-! ## The first universal correction polynomials -/

/-- The zeroth endpoint-transfer polynomial is one. -/
@[simp] theorem endpointTransferPolynomial_zero :
    endpointTransferPolynomial 0 = 1 := by
  simp [endpointTransferPolynomial]

/-- The first endpoint-transfer polynomial is `-X²/2`. -/
theorem endpointTransferPolynomial_one :
    endpointTransferPolynomial 1 = -(1 / 2 : ℚ) • X ^ 2 := by
  rw [show 1 = 0 + 1 by norm_num, endpointTransferPolynomial_succ]
  norm_num [Finset.sum_range_succ, endpointTransferPolynomial_zero,
    Algebra.smul_def]

/-- The second endpoint-transfer polynomial is `X⁴/8 - X³/3`. -/
theorem endpointTransferPolynomial_two :
    endpointTransferPolynomial 2 =
      (1 / 8 : ℚ) • X ^ 4 - (1 / 3 : ℚ) • X ^ 3 := by
  rw [show 2 = 1 + 1 by norm_num, endpointTransferPolynomial_succ]
  norm_num [Finset.sum_range_succ, endpointTransferPolynomial_zero,
    endpointTransferPolynomial_one, Algebra.smul_def]
  polynomial

/-- The third endpoint-transfer polynomial is
`-X⁶/48 + X⁵/6 - X⁴/4`. -/
theorem endpointTransferPolynomial_three :
    endpointTransferPolynomial 3 =
      -(1 / 48 : ℚ) • X ^ 6 +
        (1 / 6 : ℚ) • X ^ 5 -
          (1 / 4 : ℚ) • X ^ 4 := by
  rw [show 3 = 2 + 1 by norm_num, endpointTransferPolynomial_succ]
  norm_num [Finset.sum_range_succ, endpointTransferPolynomial_zero,
    endpointTransferPolynomial_one,
    endpointTransferPolynomial_two, Algebra.smul_def]
  polynomial

end

end Fabius
