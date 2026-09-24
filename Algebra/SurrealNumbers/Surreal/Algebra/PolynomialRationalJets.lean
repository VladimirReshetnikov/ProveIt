import Surreal.Algebra.PolynomialInverseJet
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Derivatives of reciprocal polynomial jets

The coefficients in `polynomial:eq:inversejet` in
`docs/surcomplex/polynomial-algebra/article.tex` are the iterated formal
derivatives of the reciprocal Taylor series divided by factorials.
We use Mathlib's formal power-series derivative and prove a polynomial
numerator recurrence for these derivatives.

These are algebraic formal derivatives. No analytic limit or global
derivative operator on `RatFunc` is introduced.
-/

namespace Surreal.FinitePolynomial

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

/-- Iterating formal differentiation recovers coefficients, with the
factorial normalization used in `polynomial:eq:inversejet`. -/
theorem constantCoeff_iterate_powerSeries_derivative (f : PowerSeries K) (j : ℕ) :
    PowerSeries.constantCoeff ((PowerSeries.derivative K)^[j] f) =
      (j.factorial : K) * PowerSeries.coeff j f := by
  induction j generalizing f with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, PowerSeries.coeff_derivative, Nat.factorial_succ]
    push_cast
    ring

/-- Coefficients are formal derivative values at zero divided by their
factorials in characteristic zero. -/
theorem coeff_eq_iterate_powerSeries_derivative_div_factorial [CharZero K]
    (f : PowerSeries K) (j : ℕ) :
    PowerSeries.coeff j f =
      PowerSeries.constantCoeff ((PowerSeries.derivative K)^[j] f) / (j.factorial : K) := by
  rw [constantCoeff_iterate_powerSeries_derivative]
  exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))).symm

/-- Polynomial translation commutes with the formal derivative. -/
theorem derivative_taylor (q : K[X]) (a : K) :
    (taylor a q).derivative = taylor a q.derivative := by
  simp [taylor_apply, Polynomial.derivative_comp]

/-- The reciprocal rule for the Taylor series of a polynomial. Under the
nonvanishing hypothesis used below this is the actual formal inverse. -/
theorem derivative_inverse_taylor (q : K[X]) (a : K) :
    PowerSeries.derivative K ((taylor a q : PowerSeries K)⁻¹) =
      -((taylor a q : PowerSeries K)⁻¹) ^ 2 *
        (taylor a q.derivative : PowerSeries K) := by
  rw [PowerSeries.derivative_inv', PowerSeries.derivative_coe, derivative_taylor]

/-- The polynomial numerators of the successive derivatives of `1 / q`.
The recurrence is the ordinary quotient rule with denominator `q^(j+1)`. -/
def reciprocalDerivativeNumerator (q : K[X]) : ℕ → K[X]
  | 0 => 1
  | j + 1 => q * (reciprocalDerivativeNumerator q j).derivative -
      C (j + 1 : K) * q.derivative * reciprocalDerivativeNumerator q j

@[simp] theorem reciprocalDerivativeNumerator_zero (q : K[X]) :
    reciprocalDerivativeNumerator q 0 = 1 := rfl

theorem reciprocalDerivativeNumerator_succ (q : K[X]) (j : ℕ) :
    reciprocalDerivativeNumerator q (j + 1) =
      q * (reciprocalDerivativeNumerator q j).derivative -
        C (j + 1 : K) * q.derivative * reciprocalDerivativeNumerator q j := rfl

/-- Repeated reciprocal differentiation is represented by the polynomial
numerator recurrence, with denominator `q^(j+1)`. This verifies the
ordinary repeated quotient-rule computation in the formal Taylor ring. -/
theorem iterate_derivative_inverse_taylor (q : K[X]) (a : K) (hq : q.eval a ≠ 0)
    (j : ℕ) :
    (PowerSeries.derivative K)^[j] ((taylor a q : PowerSeries K)⁻¹) =
      (taylor a (reciprocalDerivativeNumerator q j) : PowerSeries K) *
        ((taylor a q : PowerSeries K)⁻¹) ^ (j + 1) := by
  have hcancel : (taylor a q : PowerSeries K) * (taylor a q : PowerSeries K)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simpa only [Polynomial.constantCoeff_coe,
      taylor_coeff_zero] using hq)
  induction j with
  | zero => simp
  | succ j ih =>
    have hnat : taylor a (j : K[X]) = (j : K[X]) := by simp [taylor_apply]
    have hcast : ((j : K[X]) : PowerSeries K) = (j : PowerSeries K) :=
      map_natCast (Polynomial.coeToPowerSeries.ringHom (R := K)) j
    have hpower : (taylor a q : PowerSeries K) *
        ((taylor a q : PowerSeries K)⁻¹) ^ (j + 2) =
          ((taylor a q : PowerSeries K)⁻¹) ^ (j + 1) := by
      calc
        _ = ((taylor a q : PowerSeries K) * (taylor a q : PowerSeries K)⁻¹) *
            ((taylor a q : PowerSeries K)⁻¹) ^ (j + 1) := by ring
        _ = _ := by rw [hcancel, one_mul]
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz]
    simp only [smul_eq_mul, PowerSeries.derivative_pow, derivative_inverse_taylor,
      PowerSeries.derivative_coe, derivative_taylor,
      reciprocalDerivativeNumerator_succ, map_sub, taylor_mul,
      Polynomial.coe_sub, Polynomial.coe_mul, Nat.add_sub_cancel,
      map_add, map_natCast, map_one, hnat, taylor_one,
      Polynomial.coe_add, hcast, Polynomial.coe_one, Nat.cast_add, Nat.cast_one]
    rw [← hpower]
    ring

/-- Evaluating the repeated reciprocal derivative at its Taylor center
gives the ordinary quotient-rule numerator over `q(a)^(j+1)`. -/
theorem constantCoeff_iterate_derivative_inverse_taylor (q : K[X]) (a : K)
    (hq : q.eval a ≠ 0) (j : ℕ) :
    PowerSeries.constantCoeff
        ((PowerSeries.derivative K)^[j] ((taylor a q : PowerSeries K)⁻¹)) =
      (reciprocalDerivativeNumerator q j).eval a / q.eval a ^ (j + 1) := by
  rw [iterate_derivative_inverse_taylor q a hq]
  simp [PowerSeries.constantCoeff_inv, div_eq_mul_inv]

/-- The explicit coefficients of the inverse Taylor series in
characteristic zero, obtained from repeated reciprocal differentiation. -/
theorem coeff_inverse_taylor_eq_reciprocal_numerator [CharZero K]
    (q : K[X]) (a : K) (hq : q.eval a ≠ 0) (j : ℕ) :
    PowerSeries.coeff j ((taylor a q : PowerSeries K)⁻¹) =
      (reciprocalDerivativeNumerator q j).eval a /
        (q.eval a ^ (j + 1) * (j.factorial : K)) := by
  rw [coeff_eq_iterate_powerSeries_derivative_div_factorial,
    constantCoeff_iterate_derivative_inverse_taylor q a hq, div_div]

/-- The derivative-over-factorial expression of `polynomial:eq:inversejet`
in the formal Taylor ring. For a nonvanishing denominator polynomial,
the differentiated series is its reciprocal germ at `a`. -/
theorem inverseJet_eq_sum_formal_derivatives [CharZero K]
    (q : K[X]) (a : K) (m : ℕ) :
    inverseJet q a m = ∑ j ∈ Finset.range m,
      C (PowerSeries.constantCoeff
          ((PowerSeries.derivative K)^[j] ((taylor a q : PowerSeries K)⁻¹)) /
            (j.factorial : K)) * (X - C a) ^ j := by
  rw [inverseJet_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_eq_iterate_powerSeries_derivative_div_factorial]

/-- A concrete symbolic form of `polynomial:eq:inversejet`, with the
ordinary reciprocal derivative values computed by the verified numerator
recurrence. All coefficients are finite field expressions. -/
theorem inverseJet_eq_sum_reciprocal_numerators [CharZero K]
    (q : K[X]) (a : K) (hq : q.eval a ≠ 0) (m : ℕ) :
    inverseJet q a m = ∑ j ∈ Finset.range m,
      C ((reciprocalDerivativeNumerator q j).eval a /
        (q.eval a ^ (j + 1) * (j.factorial : K))) * (X - C a) ^ j := by
  rw [inverseJet_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_inverse_taylor_eq_reciprocal_numerator q a hq]

/-- Every denominator in the explicit inverse-jet formula is nonzero. -/
theorem reciprocal_jet_denominator_ne_zero [CharZero K] (q : K[X]) (a : K)
    (hq : q.eval a ≠ 0) (j : ℕ) :
    q.eval a ^ (j + 1) * (j.factorial : K) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hq) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))

end

end Surreal.FinitePolynomial
