import FabiusFunction.ThueMorseWalsh
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.LinearCombination

/-!
# The complex half-angle factorization of a Thue--Morse block

The finite Thue--Morse product `∏_{j<m} (1 - z^{2^j})` is an identity of
commutative rings.  Evaluating it at `z = exp (i w)` and factoring each
factor through the half-angle identity turns the signed block sum into a
single phase times a product of sines.  Both steps are pure exponential
algebra over `ℂ`: no reality hypothesis, no nonvanishing hypothesis, no
analysis beyond `Complex.exp` and `Complex.sin`.

This module isolates those two facts so that the real trigonometric layer
(`ThueMorseSineProduct`) and the analytic sinc/Laplace layer
(`ThueMorseComplexProductBridge`) can both build on them without either
depending on the other.

* `one_sub_cexp_mul_I` — the **complex half-angle factorization**
  `1 - e^(iz) = -2i·e^(iz/2)·sin(z/2)`.
* `sum_thueMorseSign_cexp_eq_sin_prod` — the **complex sine-product form**
  `∑_{n<2^m} ε(n)·e^(iz)^n
     = (-2i)^m·e^(i(2^m-1)z/2)·∏_{j<m} sin(2^j·z/2)`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The complex half-angle factorization
`1 - exp (i z) = -2i * exp (i z / 2) * sin (z / 2)`. -/
theorem one_sub_cexp_mul_I (z : ℂ) :
    1 - Complex.exp (z * Complex.I) =
      -2 * Complex.I * Complex.exp ((z / 2) * Complex.I) *
        Complex.sin (z / 2) := by
  have h2sin := Complex.two_sin (z / 2)
  have hI := Complex.I_sq
  have hprod :
      Complex.exp ((z / 2) * Complex.I) *
          Complex.exp (-(z / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← add_mul,
      show z / 2 + -(z / 2) = 0 by ring,
      zero_mul, Complex.exp_zero]
  have hsq :
      Complex.exp ((z / 2) * Complex.I) *
          Complex.exp ((z / 2) * Complex.I) =
        Complex.exp (z * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination
    (Complex.I * Complex.exp ((z / 2) * Complex.I)) * h2sin +
    (Complex.exp ((z / 2) * Complex.I) *
        Complex.exp (-(z / 2) * Complex.I) -
      Complex.exp ((z / 2) * Complex.I) *
        Complex.exp ((z / 2) * Complex.I)) * hI -
    hprod + hsq

/-- The complex sine-product form of a finite Thue--Morse block:
`sum ε(n) exp(iz)^n` is one phase times the product of the dyadic sines.
There is no reality or nonvanishing hypothesis. -/
theorem sum_thueMorseSign_cexp_eq_sin_prod (z : ℂ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
        Complex.exp (z * Complex.I) ^ n =
      (-2 * Complex.I) ^ m *
        Complex.exp ((((2 ^ m - 1 : ℕ) : ℂ) * z / 2) * Complex.I) *
        ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * z) / 2) := by
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign
    (Complex.exp (z * Complex.I)) m]
  calc
    ∏ j ∈ range m, (1 - Complex.exp (z * Complex.I) ^ 2 ^ j) =
        ∏ j ∈ range m,
          (-2 * Complex.I *
            Complex.exp ((((2 : ℂ) ^ j * z) / 2) * Complex.I) *
            Complex.sin (((2 : ℂ) ^ j * z) / 2)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      have hz : Complex.exp (z * Complex.I) ^ 2 ^ j =
          Complex.exp (((2 : ℂ) ^ j * z) * Complex.I) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hz, one_sub_cexp_mul_I]
    _ = (-2 * Complex.I) ^ m *
          (∏ j ∈ range m,
            Complex.exp ((((2 : ℂ) ^ j * z) / 2) * Complex.I)) *
          ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * z) / 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range]
    _ = (-2 * Complex.I) ^ m *
          Complex.exp ((((2 ^ m - 1 : ℕ) : ℂ) * z / 2) * Complex.I) *
          ∏ j ∈ range m, Complex.sin (((2 : ℂ) ^ j * z) / 2) := by
      congr 2
      rw [← Complex.exp_sum]
      congr 1
      rw [← Finset.sum_mul]
      congr 1
      have hgeom : ∑ j ∈ range m, ((2 : ℂ) ^ j) =
          ((2 ^ m - 1 : ℕ) : ℂ) := by
        have h := sum_range_two_pow m
        rw [← h]
        push_cast
        ring
      rw [← Finset.sum_div, ← Finset.sum_mul, hgeom]

end Fabius
