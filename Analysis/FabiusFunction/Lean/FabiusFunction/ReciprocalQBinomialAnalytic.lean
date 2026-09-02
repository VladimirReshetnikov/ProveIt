import FabiusFunction.QBinomialTheoremInfinite

/-!
# The reciprocal finite `q`-binomial theorem, analytically

For `‖q‖ < 1` and `‖z‖ < 1` in a complete normed field,

`1 / (z;q)_{n+1} = ∑_{k ≥ 0} [n+k, k]_q z^k`.

This is the infinite `q`-binomial theorem `∑_k (a;q)_k/(q;q)_k z^k = (az;q)_∞/(z;q)_∞` at
`a = q^{n+1}`: the coefficient `(q^{n+1};q)_k/(q;q)_k` is the Gaussian coefficient `[n+k,k]_q`
(`finiteQPochhammerIn_self_mul_gaussianBinomial`), and the quotient of infinite products
telescopes to `1/(z;q)_{n+1}` (`qPochhammerInfIn_eq_finite_mul_shift`).  The formal version in
`R[[X]]` is `prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries` of
`SymmetricFunctionGenerating`.

## Main declarations

* `hasSum_gaussianBinomial_add_mul_pow`, `tsum_gaussianBinomial_add_mul_pow`.
-/

set_option autoImplicit false

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The reciprocal finite `q`-binomial theorem**: for `‖q‖ < 1` and `‖z‖ < 1`,
`∑_{k ≥ 0} [n+k, k]_q z^k = 1/(z;q)_{n+1}`. -/
theorem hasSum_gaussianBinomial_add_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => gaussianBinomial q (n + k) k * z ^ k)
      (1 / finiteQPochhammerIn z q (n + 1)) := by
  have h := hasSum_qBinomial_theorem hq (q ^ (n + 1)) hz
  have hz0 : qPochhammerInfIn z q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz
  have hprod := qPochhammerInfIn_eq_finite_mul_shift z hq (n + 1)
  have hfin : finiteQPochhammerIn z q (n + 1) ≠ 0 := fun h0 => hz0 (by rw [hprod, h0, zero_mul])
  have hinf : qPochhammerInfIn (z * q ^ (n + 1)) q ≠ 0 := fun h0 => hz0 (by rw [hprod, h0, mul_zero])
  have hshift : qPochhammerInfIn (q ^ (n + 1) * z) q / qPochhammerInfIn z q =
      1 / finiteQPochhammerIn z q (n + 1) := by
    rw [hprod, mul_comm (q ^ (n + 1)) z]
    field_simp
  rw [hshift] at h
  refine h.congr_fun fun k => ?_
  have hqk : finiteQPochhammerIn q q k ≠ 0 := finiteQPochhammerIn_self_ne_zero hq k
  have hG := finiteQPochhammerIn_self_mul_gaussianBinomial q (n := n + k) (k := k) (by omega)
  rw [show n + k - k + 1 = n + 1 by omega] at hG
  rw [← hG, mul_div_cancel_left₀ _ hqk]

/-- The summed form: `∑' k, [n+k, k]_q z^k = 1/(z;q)_{n+1}` for `‖q‖ < 1`, `‖z‖ < 1`. -/
theorem tsum_gaussianBinomial_add_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    ∑' k : ℕ, gaussianBinomial q (n + k) k * z ^ k = 1 / finiteQPochhammerIn z q (n + 1) :=
  (hasSum_gaussianBinomial_add_mul_pow hq n hz).tsum_eq

end Fabius
