import FabiusFunction.BaselineDecay
import FabiusFunction.RenormalizationIdentity
import FabiusFunction.SincProductShells

/-!
# Arbitrary-prefix bounds for the Rvachev sinc product

Peeling an arbitrary initial segment from the Rvachev product gives more than
the usual one-factor estimate.  For every real `x` and every `K : ℕ`, the
total identity

`(π |x|)^K · ‖Φ(x)‖ =
  2^(K.choose 2) · (∏ j < K, |sin (π x / 2^j)|) · ‖Φ(x / 2^K)‖`

keeps both removable boundary cases: at `x = 0` no division is performed,
and at `K = 0` both sides are simply `‖Φ(x)‖`.  Bounding the finite sine
prefix and the remaining sinc-product tail by one yields

`(π |x|)^K · ‖Φ(x)‖ ≤ 2^(K.choose 2)`.

Only the final divided form requires `x ≠ 0`; unlike the informal
selected-factor estimate, it needs no positivity assumption on `K`.  Its
constant is exactly
`2^(K(K-1)/2) / π^K`, since `K.choose 2 = K(K-1)/2`.

The proof reuses three earlier foundations:

* `rvachevFourierProduct_shell`, the exact finite-prefix/tail decomposition;
* `abs_mul_norm_complexSinc_ofReal`, the total real sinc identity;
* `norm_rvachevFourierProduct_le_one`, the global real-axis tail bound.

Thus no convergence or decay argument is repeated here.
-/

set_option autoImplicit false

open Finset

namespace Fabius

private theorem prod_range_two_pow_eq_pow_choose_two (K : ℕ) :
    ∏ j ∈ range K, (2 : ℝ) ^ j = (2 : ℝ) ^ (K.choose 2) := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- **Exact arbitrary-prefix identity.**  Clearing the denominators of the
first `K` sinc factors gives, for every real `x`,

`(π |x|)^K · ‖Φ(x)‖ =
  2^(K.choose 2) · (∏ j < K, |sin (π x / 2^j)|) · ‖Φ(x / 2^K)‖`.

This is total in both variables.  In particular, it includes the removable
case `x = 0` and the empty prefix `K = 0`. -/
theorem norm_rvachevFourierProduct_prefix_cross (K : ℕ) (x : ℝ) :
    (Real.pi * |x|) ^ K * ‖rvachevFourierProduct (x : ℂ)‖ =
      (2 : ℝ) ^ (K.choose 2) *
        (∏ j ∈ range K, |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ := by
  have harg : ∀ j : ℕ,
      (Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j =
        ((Real.pi * x / (2 : ℝ) ^ j : ℝ) : ℂ) := by
    intro j
    push_cast
    ring
  have htail :
      (x : ℂ) / (2 : ℂ) ^ K =
        ((x / (2 : ℝ) ^ K : ℝ) : ℂ) := by
    push_cast
    ring
  have hfactor : ∀ j ∈ range K,
      (Real.pi * |x|) *
          ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖ =
        (2 : ℝ) ^ j *
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)| := by
    intro j _
    have htwo : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have habs :
        |Real.pi * x / (2 : ℝ) ^ j| =
          (Real.pi * |x|) / (2 : ℝ) ^ j := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j)]
    have hscale :
        Real.pi * |x| =
          (2 : ℝ) ^ j * |Real.pi * x / (2 : ℝ) ^ j| := by
      rw [habs]
      calc
        Real.pi * |x| =
            (Real.pi * |x| / (2 : ℝ) ^ j) * (2 : ℝ) ^ j :=
          (div_mul_cancel₀ _ htwo).symm
        _ = (2 : ℝ) ^ j * (Real.pi * |x| / (2 : ℝ) ^ j) :=
          mul_comm _ _
    rw [harg]
    calc
      (Real.pi * |x|) *
          ‖complexSinc ((Real.pi * x / (2 : ℝ) ^ j : ℝ) : ℂ)‖ =
          ((2 : ℝ) ^ j * |Real.pi * x / (2 : ℝ) ^ j|) *
            ‖complexSinc ((Real.pi * x / (2 : ℝ) ^ j : ℝ) : ℂ)‖ := by
        rw [hscale]
      _ = (2 : ℝ) ^ j *
          (|Real.pi * x / (2 : ℝ) ^ j| *
            ‖complexSinc ((Real.pi * x / (2 : ℝ) ^ j : ℝ) : ℂ)‖) := by
        ring
      _ = (2 : ℝ) ^ j *
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)| := by
        rw [abs_mul_norm_complexSinc_ofReal]
  have hpowprod :
      (Real.pi * |x|) ^ K *
          (∏ j ∈ range K,
            ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖) =
        ∏ j ∈ range K,
          (Real.pi * |x|) *
            ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖ := by
    simpa only [Finset.card_range] using
      (Finset.pow_card_mul_prod
        (s := range K)
        (f := fun j : ℕ =>
          ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖)
        (b := Real.pi * |x|))
  rw [rvachevFourierProduct_shell K (x : ℂ), norm_mul, norm_prod, htail]
  calc
    (Real.pi * |x|) ^ K *
        ((∏ j ∈ range K,
          ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖) *
          ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖) =
      ((Real.pi * |x|) ^ K *
        (∏ j ∈ range K,
          ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖)) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ := by
      ring
    _ = (∏ j ∈ range K,
          (Real.pi * |x|) *
            ‖complexSinc ((Real.pi : ℂ) * (x : ℂ) / (2 : ℂ) ^ j)‖) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ := by
      rw [hpowprod]
    _ = (∏ j ∈ range K,
          (2 : ℝ) ^ j *
            |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ := by
      rw [Finset.prod_congr rfl hfactor]
    _ = ((∏ j ∈ range K, (2 : ℝ) ^ j) *
          (∏ j ∈ range K,
            |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|)) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ := by
      rw [Finset.prod_mul_distrib]
    _ = (2 : ℝ) ^ (K.choose 2) *
        (∏ j ∈ range K,
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ := by
      rw [prod_range_two_pow_eq_pow_choose_two]

/-- **Total selected-factor bound.**  For every real `x` and every natural
`K`, including `x = 0` and `K = 0`,

`(π |x|)^K · ‖Φ(x)‖ ≤ 2^(K.choose 2)`.

It follows from the exact prefix identity by bounding every sine factor and
the remaining sinc-product tail by one. -/
theorem norm_rvachevFourierProduct_prefix_cross_le (K : ℕ) (x : ℝ) :
    (Real.pi * |x|) ^ K * ‖rvachevFourierProduct (x : ℂ)‖ ≤
      (2 : ℝ) ^ (K.choose 2) := by
  rw [norm_rvachevFourierProduct_prefix_cross K x]
  have hsine :
      (∏ j ∈ range K,
        |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) ≤ 1 :=
    Finset.prod_le_one
      (fun j _ => abs_nonneg (Real.sin (Real.pi * x / (2 : ℝ) ^ j)))
      (fun j _ => Real.abs_sin_le_one _)
  have htail :
      ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ ≤ 1 :=
    norm_rvachevFourierProduct_le_one _
  have hprefixTail :
      (∏ j ∈ range K,
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ ≤ 1 := by
    calc
      (∏ j ∈ range K,
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
          ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ ≤
        (1 : ℝ) * 1 :=
          mul_le_mul hsine htail (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc
    (2 : ℝ) ^ (K.choose 2) *
        (∏ j ∈ range K,
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
        ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖ =
      (2 : ℝ) ^ (K.choose 2) *
        ((∏ j ∈ range K,
          |Real.sin (Real.pi * x / (2 : ℝ) ^ j)|) *
          ‖rvachevFourierProduct ((x / (2 : ℝ) ^ K : ℝ) : ℂ)‖) := by
        ring
    _ ≤ (2 : ℝ) ^ (K.choose 2) * 1 :=
      mul_le_mul_of_nonneg_left hprefixTail (by positivity)
    _ = (2 : ℝ) ^ (K.choose 2) := mul_one _

/-- **Arbitrary inverse-power decay.**  For `x ≠ 0` and any `K : ℕ`,

`‖Φ(x)‖ ≤ 2^(K.choose 2) / (π |x|)^K`.

This is the selected-factor estimate with constant
`2^(K(K-1)/2) / π^K`.  The informal assumption `1 ≤ K` is unnecessary:
at `K = 0` the statement is exactly the global bound `‖Φ(x)‖ ≤ 1`. -/
theorem norm_rvachevFourierProduct_le_prefix_div
    (K : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ‖rvachevFourierProduct (x : ℂ)‖ ≤
      (2 : ℝ) ^ (K.choose 2) / (Real.pi * |x|) ^ K := by
  have hden : 0 < (Real.pi * |x|) ^ K :=
    pow_pos (mul_pos Real.pi_pos (abs_pos.mpr hx)) K
  exact (le_div_iff₀' hden).2
    (norm_rvachevFourierProduct_prefix_cross_le K x)

end Fabius
