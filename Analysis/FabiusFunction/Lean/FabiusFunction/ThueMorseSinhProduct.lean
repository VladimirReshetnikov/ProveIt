import FabiusFunction.ThueMorseBooleanCube
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The centered Thue–Morse sinh product

The real, hyperbolic twin of the sine-product form: for every `t : ℝ`,

`∑_{n<2ᵐ} εₙ·e^{(n − cₘ)t} = (−2)ᵐ·∏_{j<m} sinh(2ʲt/2)`,  `cₘ = (2ᵐ−1)/2`.

Centering the exponents at `cₘ = (2ᵐ−1)/2` — the mean of `0,…,2ᵐ−1` —
is exactly what turns the Thue–Morse exponential sum into a *product of
sinh's*, with no exponential prefactor left over.  The mechanism is one
factorization,

`1 − e^u = −2·e^{u/2}·sinh(u/2)`,

applied to `u = 2ʲt`; the leftover prefactors multiply to `e^{cₘt}`
because `∑_{j<m} 2ʲ/2 = cₘ`, which is the sum the centering cancels.

The companion `ThueMorseSineProduct.sum_thueMorseSign_exp_eq_sin_prod`
does the same on the unit circle, and both descend from the same
all-rings identity `prod_one_sub_pow_eq_sum_thueMorseSign`.  This is the
form the Laplace-side moment computations want, since every factor is
real and the centering makes the two ends of the sum symmetric.

* `one_sub_exp_eq_sinh` — the factorization, for every real `u`.
* `sum_thueMorseSign_exp_eq_sinh_prod` — the uncentered form.
* `sum_thueMorseSign_exp_centered_eq_sinh_prod` — **the centered form**.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- **The hyperbolic factorization**: `1 − eᵘ = −2·e^{u/2}·sinh(u/2)`. -/
theorem one_sub_exp_eq_sinh (u : ℝ) :
    1 - Real.exp u = -2 * Real.exp (u / 2) * Real.sinh (u / 2) := by
  rw [Real.sinh_eq]
  have hsplit : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]
    ring_nf
  have hinv : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp
  nlinarith [hsplit, hinv]

/-- The Thue–Morse exponential sum as a sinh product, uncentered. -/
theorem sum_thueMorseSign_exp_eq_sinh_prod (t : ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℝ) * Real.exp (n * t) =
      (-2) ^ m * Real.exp ((2 ^ m - 1) / 2 * t) *
        ∏ j ∈ Finset.range m, Real.sinh (2 ^ j * t / 2) := by
  have hpow : ∀ n : ℕ, Real.exp t ^ n = Real.exp (n * t) := by
    intro n
    rw [← Real.exp_nat_mul]
  have hring := prod_one_sub_pow_eq_sum_thueMorseSign (Real.exp t) m
  have hsum : ∑ n ∈ Finset.range (2 ^ m),
      ((thueMorseSign n : ℤ) : ℝ) * Real.exp t ^ n =
      ∑ n ∈ Finset.range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℝ) * Real.exp (n * t) :=
    Finset.sum_congr rfl (fun n _ => by rw [hpow])
  rw [hsum] at hring
  rw [← hring]
  -- factor every term hyperbolically
  have hfac : ∀ j ∈ Finset.range m,
      1 - Real.exp t ^ (2 ^ j) =
        -2 * Real.exp ((2:ℝ) ^ j * t / 2) *
          Real.sinh ((2:ℝ) ^ j * t / 2) := by
    intro j _
    rw [hpow, show ((2 ^ j : ℕ) : ℝ) * t = (2:ℝ) ^ j * t by push_cast; ring]
    exact one_sub_exp_eq_sinh ((2:ℝ) ^ j * t)
  rw [Finset.prod_congr rfl hfac]
  -- the leftover prefactors multiply to `exp (cₘ t)`
  have hexp : ∑ j ∈ Finset.range m, (2:ℝ) ^ j * t / 2 =
      (2 ^ m - 1) / 2 * t := by
    have hgeo : ∑ j ∈ Finset.range m, (2:ℝ) ^ j = 2 ^ m - 1 := by
      rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) m]
      ring
    have hterm : ∀ j : ℕ, (2:ℝ) ^ j * t / 2 = (2:ℝ) ^ j * (t / 2) :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_mul,
      hgeo]
    ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, ← Real.exp_sum, hexp]

/-- **The centered sinh product**: centering the exponents at the mean
`cₘ = (2ᵐ−1)/2` removes the exponential prefactor entirely. -/
theorem sum_thueMorseSign_exp_centered_eq_sinh_prod (t : ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℝ) *
          Real.exp ((n - (2 ^ m - 1) / 2) * t) =
      (-2) ^ m * ∏ j ∈ Finset.range m, Real.sinh (2 ^ j * t / 2) := by
  have hkey := sum_thueMorseSign_exp_eq_sinh_prod t m
  have hc : Real.exp ((2 ^ m - 1) / 2 * t) ≠ 0 := Real.exp_ne_zero _
  have hsplit : ∑ n ∈ Finset.range (2 ^ m),
      ((thueMorseSign n : ℤ) : ℝ) *
        Real.exp (((n : ℝ) - (2 ^ m - 1) / 2) * t) =
      (∑ n ∈ Finset.range (2 ^ m),
        ((thueMorseSign n : ℤ) : ℝ) * Real.exp ((n : ℝ) * t)) /
        Real.exp ((2 ^ m - 1) / 2 * t) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  rw [hsplit, hkey]
  field_simp

end Fabius
