import FabiusFunction.ThueMorseBooleanCube
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Thue–Morse trigonometric polynomial and the Riesz product

Evaluating the master product on the unit circle turns the signed block
sum into a trigonometric polynomial whose squared modulus is a finite
Riesz product.  This module opens the complex-Fourier layer of the atlas
with its exact algebraic part:

* `normSq_one_sub_exp` — `|1 - e^(iθ)|² = 2 - 2cos θ`.
* `normSq_sum_thueMorseSign_exp` — the **finite Riesz product**:
  `|∑_{n<2^m} ε(n)·e^(inx)|² = ∏_{j<m} (2 - 2cos(2^j x))`; dividing by
  `2^m` gives the atlas's probability density
  `ρ_m(x) = ∏ (1 - cos(2π·2^j·x))` after rescaling `x`.
* `prod_two_sub_two_cos_nonneg` — the density is nonnegative.

The evaluation at `x = -2πk/2^m` specializes to the dyadic discrete
Fourier transform; its closed sine form and the integral normalization
`∫ρ_m = 1` remain open.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `|1 - e^(iθ)|² = 2 - 2cos θ`. -/
theorem normSq_one_sub_exp (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
      2 - 2 * Real.cos θ := by
  have hre : (1 - Complex.exp (θ * Complex.I)).re = 1 - Real.cos θ := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (1 - Complex.exp (θ * Complex.I)).im = -Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  rw [Complex.normSq_apply, hre, him]
  have hpyth := Real.sin_sq_add_cos_sq θ
  ring_nf
  nlinarith [hpyth]

/-- **The finite Riesz product.**  On the unit circle the squared modulus
of the signed Thue–Morse block polynomial factorizes:
`|∑_{n<2^m} ε(n)·e^(inx)|² = ∏_{j<m} (2 - 2cos(2^j·x))`. -/
theorem normSq_sum_thueMorseSign_exp (x : ℝ) (m : ℕ) :
    Complex.normSq (∑ n ∈ range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℂ) * Complex.exp (x * Complex.I) ^ n) =
      ∏ j ∈ range m, (2 - 2 * Real.cos (2 ^ j * x)) := by
  rw [← prod_one_sub_pow_eq_sum_thueMorseSign (Complex.exp (x * Complex.I)) m,
    map_prod Complex.normSq _ (range m)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hexp : Complex.exp (x * Complex.I) ^ 2 ^ j =
      Complex.exp ((2 ^ j * x : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp, normSq_one_sub_exp]

/-- The Riesz factors are nonnegative, hence so is the density. -/
theorem prod_two_sub_two_cos_nonneg (x : ℝ) (m : ℕ) :
    0 ≤ ∏ j ∈ range m, (2 - 2 * Real.cos (2 ^ j * x)) := by
  refine Finset.prod_nonneg fun j _ => ?_
  have := Real.cos_le_one (2 ^ j * x)
  linarith

end Fabius
