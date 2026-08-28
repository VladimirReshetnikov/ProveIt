import FabiusFunction.RenormalizationIdentity
import FabiusFunction.SincProductShells
import FabiusFunction.BaselineDecay

/-!
# The explicit `K`-shell envelope of `Φ`

Iterating the renormalization identity `K` times and taking moduli
turns the shell factorization into a *quantitative* decay statement
with all constants exposed:

`(π|y|)^K·‖Φ(y)‖ = (∏_{k<K} |sin(πy/2ᵏ)|)·2^{K(K−1)/2}·‖Φ(y/2^K)‖`.

Three points of generality over the usual statement of this bound:

* it is an **equality**, cross-multiplied, so it holds with **no
  hypothesis on `y`** — including `y = 0`, where both sides vanish for
  `K ≥ 1`.  The division form is a corollary for `y ≠ 0`;
* the sine numerators are **kept**.  The customary corollary
  `‖Φ(y)‖ ≤ C_K|y|^{−K}` discards them, but they are what a sharp
  estimate along a ray needs, and they are exactly the lacunary product
  the rest of the development studies;
* the constant is explicit: `2^{K(K−1)/2}`, from `∑_{k<K} k`.

The mechanism is one hypothesis-free identity per factor,
`|r|·‖sinc r‖ = |sin r|` (`abs_mul_norm_complexSinc_ofReal`), which is
what removes every side condition.

* `norm_rvachevFourierProduct_shell_cross` — **the equality**.
* `norm_rvachevFourierProduct_shell_div` — the division form.
* `norm_rvachevFourierProduct_le_pow_div` — the classical corollary.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- **The explicit shell envelope, cross-multiplied**: no hypothesis on
`y`, all constants exposed, sine numerators retained. -/
theorem norm_rvachevFourierProduct_shell_cross (K : ℕ) (y : ℝ) :
    (π * |y|) ^ K * ‖rvachevFourierProduct (y : ℂ)‖ =
      (∏ k ∈ Finset.range K, |Real.sin (π * y / 2 ^ k)|) *
        2 ^ (K * (K - 1) / 2) *
        ‖rvachevFourierProduct ((y / 2 ^ K : ℝ) : ℂ)‖ := by
  have hcast : ((y / 2 ^ K : ℝ) : ℂ) = (y : ℂ) / 2 ^ K := by
    push_cast
    ring
  have hshell := rvachevFourierProduct_shell K (y : ℂ)
  rw [hcast, hshell, norm_mul, norm_prod]
  -- each factor: `|πy/2ᵏ| · ‖sinc(πy/2ᵏ)‖ = |sin(πy/2ᵏ)|`
  have hfac : ∀ k ∈ Finset.range K,
      |π * y / 2 ^ k| * ‖complexSinc ((Real.pi : ℂ) * (y : ℂ) / 2 ^ k)‖ =
        |Real.sin (π * y / 2 ^ k)| := by
    intro k _
    have hc : ((Real.pi : ℂ) * (y : ℂ) / 2 ^ k) =
        (((π * y / 2 ^ k : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hc]
    exact abs_mul_norm_complexSinc_ofReal _
  -- the product of the moduli of the arguments is the explicit constant
  have habs : ∀ k : ℕ, |π * y / 2 ^ k| = π * |y| / 2 ^ k := by
    intro k
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by positivity : (0:ℝ) < 2 ^ k)]
  have hprodarg : ∏ k ∈ Finset.range K, |π * y / 2 ^ k| =
      (π * |y|) ^ K / 2 ^ (K * (K - 1) / 2) := by
    have hsum : ∑ k ∈ Finset.range K, k = K * (K - 1) / 2 := by
      rw [Finset.sum_range_id]
    calc ∏ k ∈ Finset.range K, |π * y / 2 ^ k|
        = ∏ k ∈ Finset.range K, (π * |y|) / 2 ^ k :=
          Finset.prod_congr rfl (fun k _ => habs k)
      _ = (π * |y|) ^ K / ∏ k ∈ Finset.range K, (2:ℝ) ^ k := by
          rw [Finset.prod_div_distrib, Finset.prod_const,
            Finset.card_range]
      _ = (π * |y|) ^ K / 2 ^ (K * (K - 1) / 2) := by
          rw [Finset.prod_pow_eq_pow_sum, hsum]
  -- assemble
  have hcombine : ∏ k ∈ Finset.range K, |Real.sin (π * y / 2 ^ k)| =
      ((π * |y|) ^ K / 2 ^ (K * (K - 1) / 2)) *
        ∏ k ∈ Finset.range K,
          ‖complexSinc ((Real.pi : ℂ) * (y : ℂ) / 2 ^ k)‖ := by
    rw [← hprodarg, ← Finset.prod_mul_distrib]
    exact (Finset.prod_congr rfl hfac).symm
  rw [hcombine]
  have h2 : ((2:ℝ) ^ (K * (K - 1) / 2)) ≠ 0 := by positivity
  field_simp

/-- The division form, for `y ≠ 0`. -/
theorem norm_rvachevFourierProduct_shell_div {y : ℝ} (hy : y ≠ 0)
    (K : ℕ) :
    ‖rvachevFourierProduct (y : ℂ)‖ =
      (∏ k ∈ Finset.range K, |Real.sin (π * y / 2 ^ k)|) *
        2 ^ (K * (K - 1) / 2) *
        ‖rvachevFourierProduct ((y / 2 ^ K : ℝ) : ℂ)‖ /
        (π * |y|) ^ K := by
  have hpos : (0:ℝ) < (π * |y|) ^ K := by
    have : (0:ℝ) < π * |y| := mul_pos Real.pi_pos (abs_pos.mpr hy)
    positivity
  rw [eq_div_iff (ne_of_gt hpos), mul_comm]
  exact norm_rvachevFourierProduct_shell_cross K y

/-- **The classical corollary**: discarding the sine numerators and the
tail modulus gives `‖Φ(y)‖ ≤ 2^{K(K−1)/2}/(π|y|)^K`, an explicit
`C_K|y|^{−K}` for every `K`. -/
theorem norm_rvachevFourierProduct_le_pow_div {y : ℝ} (hy : y ≠ 0)
    (K : ℕ) :
    ‖rvachevFourierProduct (y : ℂ)‖ ≤
      2 ^ (K * (K - 1) / 2) / (π * |y|) ^ K := by
  have hpos : (0:ℝ) < (π * |y|) ^ K := by
    have : (0:ℝ) < π * |y| := mul_pos Real.pi_pos (abs_pos.mpr hy)
    positivity
  rw [le_div_iff₀ hpos, mul_comm]
  rw [norm_rvachevFourierProduct_shell_cross K y]
  have hsin : (∏ k ∈ Finset.range K, |Real.sin (π * y / 2 ^ k)|) ≤ 1 :=
    Finset.prod_le_one (fun k _ => abs_nonneg _)
      (fun k _ => Real.abs_sin_le_one _)
  have htail : ‖rvachevFourierProduct ((y / 2 ^ K : ℝ) : ℂ)‖ ≤ 1 :=
    norm_rvachevFourierProduct_le_one _
  have hc : (0:ℝ) < 2 ^ (K * (K - 1) / 2) := by positivity
  calc (∏ k ∈ Finset.range K, |Real.sin (π * y / 2 ^ k)|) *
        2 ^ (K * (K - 1) / 2) *
        ‖rvachevFourierProduct ((y / 2 ^ K : ℝ) : ℂ)‖
      ≤ 1 * 2 ^ (K * (K - 1) / 2) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hsin hc.le) htail
          (norm_nonneg _)
        positivity
    _ = 2 ^ (K * (K - 1) / 2) := by ring

end Fabius
