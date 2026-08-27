import FabiusFunction.SaddleExpansionAlgebra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

The construction is universal: evaluating the polynomial at an element `z`
of any commutative rational algebra gives the exponential coefficient formed
directly in that algebra.  Thus the same finite objects apply to real or
complex endpoint moments, formal polynomial variables, and future
parameterized coefficient rings.

No analytic use of `(1 - z t)^(1/t)` is made here.  The theorem proved is the
exact formal exponential identity, with no convergence or branch hypotheses.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial PowerSeries

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
  rfl

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
first `N` universal correction polynomials as an ordinary polynomial in the
formal endpoint parameter. -/
theorem trunc_endpointTransferSeries (N : ℕ) :
    PowerSeries.trunc N endpointTransferSeries =
      ∑ r ∈ range N, Polynomial.monomial r
        (endpointTransferPolynomial r) := by
  rw [endpointTransferSeries,
    PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [SaddleExpansion.coeff_expSeries]
  rfl

/-! ## Universality under evaluation -/

/-- The scalar exponent coefficients obtained after evaluating the universal
polynomial variable at `z` in a commutative rational algebra. -/
def endpointTransferExponentAt
    {R : Type*} [CommRing R] [Algebra ℚ R] (z : R) : ℕ → R
  | 0 => 0
  | n + 1 => algebraMap ℚ R (-(n + 2 : ℚ)⁻¹) * z ^ (n + 2)

/-- **Universal evaluation theorem.**  Evaluating `P_r` at `z` in any
commutative rational algebra is exactly the `r`-th exponential coefficient
formed from the scalar exponent
`-z²t/2 - z³t²/3 - ⋯` in that algebra. -/
theorem aeval_endpointTransferPolynomial
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (z : R) (r : ℕ) :
    Polynomial.aeval z (endpointTransferPolynomial r) =
      SaddleExpansion.expCoeff (endpointTransferExponentAt z) r := by
  rw [endpointTransferPolynomial,
    SaddleExpansion.map_expCoeff (Polynomial.aeval z)
      endpointTransferExponentCoefficient r]
  apply congrArg (fun E : ℕ → R => SaddleExpansion.expCoeff E r)
  funext n
  cases n with
  | zero => simp [endpointTransferExponentAt,
      endpointTransferExponentCoefficient]
  | succ n => simp [endpointTransferExponentAt,
      endpointTransferExponentCoefficient]

/-! ## The first universal correction polynomials -/

/-- The zeroth endpoint-transfer polynomial is one. -/
@[simp] theorem endpointTransferPolynomial_zero :
    endpointTransferPolynomial 0 = 1 := by
  simp [endpointTransferPolynomial]

/-- The first endpoint-transfer polynomial is `-X²/2`. -/
theorem endpointTransferPolynomial_one :
    endpointTransferPolynomial 1 = -(1 / 2 : ℚ) • X ^ 2 := by
  norm_num [endpointTransferPolynomial, endpointTransferExponentCoefficient,
    SaddleExpansion.expCoeff] <;> ring

/-- The second endpoint-transfer polynomial is `X⁴/8 - X³/3`. -/
theorem endpointTransferPolynomial_two :
    endpointTransferPolynomial 2 =
      (1 / 8 : ℚ) • X ^ 4 - (1 / 3 : ℚ) • X ^ 3 := by
  norm_num [endpointTransferPolynomial, endpointTransferExponentCoefficient,
    SaddleExpansion.expCoeff] <;> ring

/-- The third endpoint-transfer polynomial is
`-X⁶/48 + X⁵/6 - X⁴/4`. -/
theorem endpointTransferPolynomial_three :
    endpointTransferPolynomial 3 =
      -(1 / 48 : ℚ) • X ^ 6 +
        (1 / 6 : ℚ) • X ^ 5 -
          (1 / 4 : ℚ) • X ^ 4 := by
  norm_num [endpointTransferPolynomial, endpointTransferExponentCoefficient,
    SaddleExpansion.expCoeff] <;> ring

end

end Fabius
