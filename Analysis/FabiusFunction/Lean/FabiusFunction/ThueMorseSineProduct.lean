import FabiusFunction.ThueMorseFourier
import FabiusFunction.ThueMorseWalsh

/-!
# The sine-product form of the Thue–Morse trigonometric polynomial

Factoring each `1 - e^(i·2^j x)` through the half-angle identity turns
the signed block sum on the unit circle into an explicit product of
sines times a single phase — the closed form behind the dyadic discrete
Fourier transform.

* `one_sub_exp_mul_I` — the **half-angle factorization**
  `1 - e^(iv) = -2i·e^(iv/2)·sin(v/2)`, by pure exponential algebra.
* `sum_thueMorseSign_exp_eq_sin_prod` — the **sine-product form**:
  `∑_{n<2^m} ε(n)·e^(inx)
     = (-2i)^m·e^(i(2^m-1)x/2)·∏_{j<m} sin(2^j·x/2)`.
  At `x = -2πk/2^m` this is the atlas's closed dyadic DFT; taking
  `normSq` recovers the Riesz product, the phase having modulus one.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Half-angle factorization**: `1 - e^(iv) = -2i·e^(iv/2)·sin(v/2)`. -/
theorem one_sub_exp_mul_I (v : ℝ) :
    1 - Complex.exp ((v : ℂ) * Complex.I) =
      -2 * Complex.I * Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) *
        ((Real.sin (v / 2) : ℂ)) := by
  have h2sin := Complex.two_sin (((v / 2 : ℝ) : ℂ))
  have hI := Complex.I_sq
  have hprod : Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-(((v / 2 : ℝ) : ℂ)) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← add_mul,
      show ((v / 2 : ℝ) : ℂ) + -(((v / 2 : ℝ) : ℂ)) = 0 by ring,
      zero_mul, Complex.exp_zero]
  have hsq : Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((v : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← add_mul]
    congr 2
    push_cast
    ring
  rw [Complex.ofReal_sin]
  linear_combination
    (Complex.I * Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I)) * h2sin +
    (Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(((v / 2 : ℝ) : ℂ)) * Complex.I) -
      Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((v / 2 : ℝ) : ℂ) * Complex.I)) * hI -
    hprod + hsq

/-- **The sine-product form.**  On the unit circle,
`∑_{n<2^m} ε(n)·e^(inx)
   = (-2i)^m·e^(i(2^m-1)x/2)·∏_{j<m} sin(2^j·x/2)`. -/
theorem sum_thueMorseSign_exp_eq_sin_prod (x : ℝ) (m : ℕ) :
    ∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
        Complex.exp ((x : ℂ) * Complex.I) ^ n =
      (-2 * Complex.I) ^ m *
        Complex.exp ((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) * Complex.I) *
        ∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ)) := by
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign
    (Complex.exp ((x : ℂ) * Complex.I)) m]
  calc ∏ j ∈ range m,
        (1 - Complex.exp ((x : ℂ) * Complex.I) ^ 2 ^ j)
      = ∏ j ∈ range m, (-2 * Complex.I *
          Complex.exp (((2 ^ j * x / 2 : ℝ) : ℂ) * Complex.I) *
          ((Real.sin (2 ^ j * x / 2) : ℂ))) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        have hz : Complex.exp ((x : ℂ) * Complex.I) ^ 2 ^ j =
            Complex.exp (((2 ^ j * x : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_nat_mul]
          congr 1
          push_cast
          ring
        rw [hz, one_sub_exp_mul_I (2 ^ j * x)]
    _ = (-2 * Complex.I) ^ m *
          (∏ j ∈ range m,
            Complex.exp (((2 ^ j * x / 2 : ℝ) : ℂ) * Complex.I)) *
          ∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_range]
    _ = (-2 * Complex.I) ^ m *
          Complex.exp ((((2 ^ m - 1 : ℕ) : ℝ) * x / 2 : ℝ) * Complex.I) *
          ∏ j ∈ range m, ((Real.sin (2 ^ j * x / 2) : ℂ)) := by
        congr 2
        rw [← Complex.exp_sum]
        congr 1
        rw [← Finset.sum_mul]
        congr 1
        have hgeom : ∑ j ∈ range m, ((2 : ℂ)) ^ j =
            ((2 ^ m - 1 : ℕ) : ℂ) := by
          have h := sum_range_two_pow m
          rw [← h]
          push_cast
          ring
        push_cast
        rw [← Finset.sum_div, ← Finset.sum_mul, hgeom]

end Fabius
