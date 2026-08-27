import FabiusFunction.SincProductShells
import FabiusFunction.SharpGelfondBound

/-!
# The exact peak ray of the Rvachev sinc product

Document 6 of the second-wave Fourier-decay corpus states — and the
second-wave audit verified to 38 digits — that along the geometric ray
`x = 2ᵏ·(2/3)` the normalized transform is **exactly constant**:
`|Φ(2ᵏ·2/3)| = C₊·E_{κ∞}(2ᵏ·2/3)` for every `k ≥ 0`.  The reason is
that the doubling orbit of the mantissa is exactly the period-two
cycle `{1/3, 2/3}` of the Gelfond maximizer, so every sine factor of
the dyadic shell equals `√3/2` exactly, with no asymptotics anywhere.

This file proves the identity in its exact product form: combining the
shell factorization `norm_rvachevFourierProduct_two_pow_mul` of
`SincProductShells` with the exact orbit values
`abs_sin_two_pow_third` of `SharpGelfondBound`,

`‖Φ(2ᵏ·(2/3))‖ = (√3/2)ᵏ / (2^(k(k+1)/2)·(2π/3)ᵏ) · ‖Φ(2/3)‖`.

Every ingredient of the decay dictionary is visible: the triangular
power `2^(k(k+1)/2)` is the universal `exp(-(log x)²/(2 log 2))`
factor, the ratio `(√3/2)ᵏ/(2π/3)ᵏ` is the extremal per-shell rate
that produces the power `x^{-κ∞}`, and the constant `‖Φ(2/3)‖`
carries the audit's `C₊ = W_{κ∞}(2/3) = 0.13912977473482934529…`
after the exponent bookkeeping of `shell_exponent_identity`.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- Along the ray through `2/3`, every dyadic shell sine factor is
exactly the Gelfond constant: `|sin (2^(j+1) π (2/3))| = √3/2`. -/
theorem abs_sin_shell_two_thirds (j : ℕ) :
    |Real.sin ((2:ℝ) ^ (j + 1) * π * (2 / 3 : ℝ))| = Real.sqrt 3 / 2 := by
  have harg : (2:ℝ) ^ (j + 1) * π * (2 / 3 : ℝ) =
      π * 2 ^ (j + 2) * (1 / 3 : ℝ) := by
    ring
  rw [harg, abs_sin_two_pow_third]

/-- **The exact peak ray**: dilating the Rvachev sinc product by `2ᵏ`
along the ray through `2/3` multiplies its modulus by exactly
`(√3/2)ᵏ / (2^(k(k+1)/2)·(2π/3)ᵏ)` — the extremal shell rate with no
error term.  This is the identity behind the exact attainment of the
envelope exponent `κ∞` on a single explicit geometric ray. -/
theorem norm_rvachevFourierProduct_two_pow_two_thirds (k : ℕ) :
    ‖rvachevFourierProduct ((2:ℂ) ^ k * ((2 / 3 : ℝ) : ℂ))‖ =
      (Real.sqrt 3 / 2) ^ k /
        ((2:ℝ) ^ (k * (k + 1) / 2) * (2 * π / 3) ^ k) *
        ‖rvachevFourierProduct (((2 / 3 : ℝ) : ℂ))‖ := by
  have h := norm_rvachevFourierProduct_two_pow_mul k (2 / 3 : ℝ)
    (by norm_num)
  have hfac : ∀ j ∈ range k,
      |Real.sin ((2:ℝ) ^ (j + 1) * π * (2 / 3 : ℝ))| = Real.sqrt 3 / 2 :=
    fun j _ => abs_sin_shell_two_thirds j
  have hnum : (∏ j ∈ range k,
      |Real.sin ((2:ℝ) ^ (j + 1) * π * (2 / 3 : ℝ))|) =
        (Real.sqrt 3 / 2) ^ k := by
    rw [Finset.prod_congr rfl hfac, Finset.prod_const, Finset.card_range]
  have habs : |(2 / 3 : ℝ)| = 2 / 3 := by
    rw [abs_of_pos]
    norm_num
  have hden : (π * |(2 / 3 : ℝ)|) ^ k = (2 * π / 3) ^ k := by
    rw [habs]
    ring_nf
  rw [h, hnum, hden]

end Fabius
