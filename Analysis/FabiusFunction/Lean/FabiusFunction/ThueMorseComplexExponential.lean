import FabiusFunction.ThueMorseBooleanCube
import Mathlib.Analysis.Complex.Exponential

/-!
# Complex exponential transforms of dyadic Thue--Morse blocks

The Boolean-cube product is a polynomial identity.  Substituting the complex
parameter `exp z` turns it into a finite exponential transform, valid for
every complex `z` and without convergence or reality hypotheses.

This module records that analytic-looking consequence in its strongest useful
finite form:

* `sum_range_two_pow_binaryWeight_cexp` is the two-parameter Hamming-weight
  transform
  `sum_{n < 2^m} u^w(n) exp(nz) = product_{j < m} (1 + u exp(2^j z))`;
* `sum_range_two_pow_binaryWeight_cexp_affine` translates the weighted
  exponent by an arbitrary complex constant;
* `sum_range_two_pow_thueMorseSign_cexp` specializes `u = -1`, giving the
  complex Thue--Morse block transform;
* `sum_range_two_pow_thueMorseSign_cexp_affine` translates the exponent by an
  arbitrary complex constant.

The two unshifted theorems transport `prod_one_add_mul_pow` and
`prod_one_sub_pow_eq_sum_thueMorseSign` through `Complex.exp_nat_mul`; the
affine forms are deliberately thin corollaries.  In particular, the real
exponential-ray and unit-circle Fourier identities are restrictions of one
common complex formula.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Weighted Boolean-cube exponential transform.**  For arbitrary complex
parameters `u` and `z`, the Hamming-weight enumerator of a dyadic block
factorizes as

`sum_{n < 2^m} u^w(n) exp(nz) = product_{j < m} (1 + u exp(2^j z))`.

The equality holds for every complex `z`; finiteness makes every convergence
hypothesis unnecessary. -/
theorem sum_range_two_pow_binaryWeight_cexp (u z : ℂ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        u ^ binaryWeight n * Complex.exp ((n : ℂ) * z) =
      ∏ j ∈ range m,
        (1 + u * Complex.exp (((2 ^ j : ℕ) : ℂ) * z)) := by
  simpa only [Complex.exp_nat_mul] using
    (prod_one_add_mul_pow u (Complex.exp z) m).symm

/-- **Affine weighted Boolean-cube exponential transform.**  Translating every
exponent by `a` contributes the common factor `exp a`, uniformly in the
Hamming-weight parameter `u`:

`sum_{n < 2^m} u^w(n) exp(a + nz)
  = exp(a) product_{j < m} (1 + u exp(2^j z))`. -/
theorem sum_range_two_pow_binaryWeight_cexp_affine
    (u a z : ℂ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        u ^ binaryWeight n * Complex.exp (a + (n : ℂ) * z) =
      Complex.exp a *
        ∏ j ∈ range m,
          (1 + u * Complex.exp (((2 ^ j : ℕ) : ℂ) * z)) := by
  rw [← sum_range_two_pow_binaryWeight_cexp u z m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.exp_add]
  ac_rfl

/-- **Complex Thue--Morse block transform.**  For every complex `z`,

`sum_{n < 2^m} ε(n) exp(nz) = product_{j < m} (1 - exp(2^j z))`.

Thus the Laplace and Fourier block products are two restrictions of the same
finite complex identity. -/
theorem sum_range_two_pow_thueMorseSign_cexp (z : ℂ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        (thueMorseSign n : ℂ) * Complex.exp ((n : ℂ) * z) =
      ∏ j ∈ range m,
        (1 - Complex.exp (((2 ^ j : ℕ) : ℂ) * z)) := by
  simpa only [Complex.exp_nat_mul] using
    (prod_one_sub_pow_eq_sum_thueMorseSign (Complex.exp z) m).symm

/-- **Affine complex Thue--Morse transform.**  Translating every exponent by
`a` contributes the single common factor `exp a`:

`sum_{n < 2^m} ε(n) exp(a + nz)
  = exp(a) product_{j < m} (1 - exp(2^j z))`.

This packages arbitrary exponential amplitude and phase shifts without
duplicating the Boolean-cube argument. -/
theorem sum_range_two_pow_thueMorseSign_cexp_affine
    (a z : ℂ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m),
        (thueMorseSign n : ℂ) * Complex.exp (a + (n : ℂ) * z) =
      Complex.exp a *
        ∏ j ∈ range m,
          (1 - Complex.exp (((2 ^ j : ℕ) : ℂ) * z)) := by
  rw [← sum_range_two_pow_thueMorseSign_cexp z m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.exp_add]
  ac_rfl

end Fabius
