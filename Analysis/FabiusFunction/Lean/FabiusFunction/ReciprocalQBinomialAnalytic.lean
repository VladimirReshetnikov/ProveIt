import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.GaussianBinomialInteger

/-!
# The reciprocal finite `q`-binomial theorem, analytically

For `‖q‖ < 1` and `‖z‖ < 1` in a complete normed field,

`1 / (z;q)_{n+1} = ∑_{k ≥ 0} [n+k, k]_q z^k`.

This is the infinite `q`-binomial theorem `∑_k (a;q)_k/(q;q)_k z^k = (az;q)_∞/(z;q)_∞` at
`a = q^{n+1}`: the coefficient `(q^{n+1};q)_k/(q;q)_k` is the Gaussian coefficient `[n+k,k]_q`
(`finiteQPochhammerIn_self_mul_gaussianBinomial`), and the quotient of infinite products
telescopes to `1/(z;q)_{n+1}` (`qPochhammerInfIn_eq_finite_mul_shift`).  That argument is
carried out for every `m` in `GaussianBinomialInteger.hasSum_reciprocal_finiteQPochhammerIn`,
of which the statement here is the case `m = n + 1` with the index `n + 1 + k - 1 = n + k`
simplified.  The formal version in `R[[X]]` is
`prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries` of `SymmetricFunctionGenerating`.

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
  rw [one_div]
  refine (hasSum_reciprocal_finiteQPochhammerIn hq (n + 1) hz).congr_fun
    fun k => ?_
  show gaussianBinomial q (n + k) k * z ^ k =
    gaussianBinomial q (n + 1 + k - 1) k * z ^ k
  rw [show n + 1 + k - 1 = n + k by omega]

/-- The summed form: `∑' k, [n+k, k]_q z^k = 1/(z;q)_{n+1}` for `‖q‖ < 1`, `‖z‖ < 1`. -/
theorem tsum_gaussianBinomial_add_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    ∑' k : ℕ, gaussianBinomial q (n + k) k * z ^ k = 1 / finiteQPochhammerIn z q (n + 1) :=
  (hasSum_gaussianBinomial_add_mul_pow hq n hz).tsum_eq

end Fabius
