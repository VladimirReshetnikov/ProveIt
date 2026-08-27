import FabiusFunction.GeometricScaleProducts
import FabiusFunction.FourierProduct

/-!
# Dyadic shell factorization of the Rvachev sinc product

Specializing the geometric-scale renormalization of
`GeometricScaleProducts` to `g = complexSinc (π·)` and `c = 2` gives the
exact dyadic factorizations that organize the whole Fourier-decay
analysis of the up-function (comparative audit, Section "The common
core"): dilating the argument of the infinite sinc product by `2ᵏ`
creates exactly the `k` sine factors of the corresponding dyadic shell,
and on the real axis their moduli split into the lacunary sine product
over the triangular power `2^(k(k+1)/2)` — the source of the universal
`exp(-(log x)²/(2 log 2))` decay factor.

* `rvachevFourierProduct_two_mul` / `rvachevFourierProduct_two_pow_mul`
  — the refinement law `Φ(2z) = sinc(2πz)·Φ(z)` and its `k`-fold
  iterate, for the standalone infinite product (no Fabius-function
  hypotheses).
* `norm_complexSinc_ofReal` — on the real axis,
  `‖sinc r‖ = |sin r| / |r|`.
* `prod_range_two_pow_succ` — the triangular power
  `∏_{j<k} 2^(j+1) = 2^(k(k+1)/2)`.
* `norm_rvachevFourierProduct_two_pow_mul` — the **shell
  factorization** of the modulus:
  `‖Φ(2ᵏ·y)‖ = (∏_{j<k} |sin (2^(j+1) π y)|) /
     (2^(k(k+1)/2) (π|y|)ᵏ) · ‖Φ(y)‖` for real `y ≠ 0`.
* `shell_exponent_identity` — the exponent bookkeeping that converts
  per-shell rates into powers of the frequency: if `L = k·a + b` then
  `-(a/2)k(k+1) - (k+1)(c+b)
     = -L²/(2a) - (1/2 + c/a)·L + Φ_c(b)`
  with the bounded mantissa term
  `Φ_c(b) = b²/(2a) + bc/a - b/2 - c`.  This is the identity through
  which every per-level mean `e^{-c}` of the audit becomes the power
  `x^{-(1/2 + c/a)}` of its decay law.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The infinite sinc product written as a geometric-scale product of
`g = complexSinc (π·)` at base `2`. -/
theorem rvachevFourierProduct_eq_tprod_scale (z : ℂ) :
    rvachevFourierProduct z =
      ∏' n : ℕ, complexSinc (Real.pi * (z / 2 ^ n)) := by
  unfold rvachevFourierProduct
  simp only [mul_div_assoc]

/-- The scale factors of the sinc product are multipliable in the
geometric-scale normalization. -/
theorem sincScaleFactors_multipliable (z : ℂ) :
    Multipliable fun n : ℕ => complexSinc (Real.pi * (z / 2 ^ n)) := by
  have h := sincFactors_multipliable z
  simpa only [mul_div_assoc] using h

/-- **Refinement law for the standalone sinc product**:
`Φ(2z) = sinc(π·2z)·Φ(z)`. -/
theorem rvachevFourierProduct_two_mul (z : ℂ) :
    rvachevFourierProduct (2 * z) =
      complexSinc (Real.pi * (2 * z)) * rvachevFourierProduct z := by
  rw [rvachevFourierProduct_eq_tprod_scale, rvachevFourierProduct_eq_tprod_scale]
  exact tprod_geom_scale (fun u => complexSinc (Real.pi * u)) two_ne_zero
    (sincScaleFactors_multipliable z)

/-- **Dyadic shell factorization**: dilating the argument of the sinc
product by `2ᵏ` creates exactly the `k` sine factors of the shell,
`Φ(2ᵏ·z) = (∏_{j<k} sinc(π·2^(j+1)·z)) · Φ(z)`. -/
theorem rvachevFourierProduct_two_pow_mul (k : ℕ) (z : ℂ) :
    rvachevFourierProduct ((2 : ℂ) ^ k * z) =
      (∏ j ∈ range k, complexSinc (Real.pi * ((2 : ℂ) ^ (j + 1) * z))) *
        rvachevFourierProduct z := by
  rw [rvachevFourierProduct_eq_tprod_scale, rvachevFourierProduct_eq_tprod_scale]
  exact tprod_geom_scale_pow (fun u => complexSinc (Real.pi * u)) two_ne_zero
    (sincScaleFactors_multipliable z) k

/-- On the real axis the complex sinc has modulus `|sin r| / |r|`. -/
theorem norm_complexSinc_ofReal (r : ℝ) (hr : r ≠ 0) :
    ‖complexSinc (r : ℂ)‖ = |Real.sin r| / |r| := by
  rw [complexSinc, if_neg (Complex.ofReal_ne_zero.mpr hr), ← Complex.ofReal_sin,
    norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- The triangular power of the dyadic shell denominators:
`∏_{j<k} 2^(j+1) = 2^(k(k+1)/2)`. -/
theorem prod_range_two_pow_succ (k : ℕ) :
    ∏ j ∈ range k, (2 : ℝ) ^ (j + 1) = 2 ^ (k * (k + 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h := Finset.sum_range_succ' (fun i : ℕ => i) k
  simp only [add_zero] at h
  calc ∑ j ∈ range k, (j + 1) = ∑ i ∈ range (k + 1), i := h.symm
    _ = (k + 1) * k / 2 := by rw [Finset.sum_range_id]; simp
    _ = k * (k + 1) / 2 := by rw [Nat.mul_comm]

/-- **Shell factorization of the modulus** (the exact dyadic
factorization of the decay audit): for real `y ≠ 0`,
`‖Φ(2ᵏ·y)‖ = (∏_{j<k} |sin(2^(j+1)·π·y)|) / (2^(k(k+1)/2)·(π·|y|)ᵏ)
  · ‖Φ(y)‖`.
The triangular power in the denominator is the source of the universal
factor `exp(-(log x)²/(2 log 2))`; the numerator is the lacunary sine
product whose statistics produce the spectrum of decay exponents. -/
theorem norm_rvachevFourierProduct_two_pow_mul (k : ℕ) (y : ℝ) (hy : y ≠ 0) :
    ‖rvachevFourierProduct ((2 : ℂ) ^ k * (y : ℂ))‖ =
      (∏ j ∈ range k, |Real.sin ((2 : ℝ) ^ (j + 1) * Real.pi * y)|) /
        ((2 : ℝ) ^ (k * (k + 1) / 2) * (Real.pi * |y|) ^ k) *
        ‖rvachevFourierProduct (y : ℂ)‖ := by
  rw [rvachevFourierProduct_two_pow_mul, norm_mul, norm_prod]
  congr 1
  have hfac : ∀ j ∈ range k,
      ‖complexSinc (Real.pi * ((2 : ℂ) ^ (j + 1) * (y : ℂ)))‖ =
        |Real.sin ((2 : ℝ) ^ (j + 1) * Real.pi * y)| /
          ((2 : ℝ) ^ (j + 1) * (Real.pi * |y|)) := by
    intro j _
    have hcast : Real.pi * ((2 : ℂ) ^ (j + 1) * (y : ℂ)) =
        (((2 : ℝ) ^ (j + 1) * Real.pi * y : ℝ) : ℂ) := by
      push_cast
      ring
    have hr : (2 : ℝ) ^ (j + 1) * Real.pi * y ≠ 0 := by
      have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
      exact mul_ne_zero (mul_ne_zero (ne_of_gt h2) Real.pi_ne_zero) hy
    rw [hcast, norm_complexSinc_ofReal _ hr]
    congr 1
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 ^ (j + 1)),
      abs_of_pos Real.pi_pos]
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    prod_range_two_pow_succ]

/-- **Exponent bookkeeping for dyadic shells** (the `κ`-algebra of the
decay audit): if `L = k·a + b` — think of `L = log x`, `a = log 2`,
`k` the shell index and `b` the log-mantissa — then the deterministic
shell cost `-(a/2)·k(k+1) - (k+1)(c+b)` rearranges exactly into
`-(L²/(2a)) - (1/2 + c/a)·L` plus a function of the mantissa alone.
Consequently a per-shell numerator rate `e^{-c(k+1)}` produces the
frequency power `x^{-(1/2 + c/a)}` next to the universal
`exp(-L²/(2a))`: this is how each mean of the lacunary sine product
turns into one exponent of the decay spectrum. -/
theorem shell_exponent_identity (a b c L k : ℝ) (ha : a ≠ 0)
    (hL : L = k * a + b) :
    -(a / 2) * (k * (k + 1)) - (k + 1) * (c + b) =
      -(L ^ 2 / (2 * a)) - (1 / 2 + c / a) * L +
        (b ^ 2 / (2 * a) + b * c / a - b / 2 - c) := by
  subst hL
  field_simp
  ring

end Fabius
