import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary transfer certificates for the GRH repository review

This file is independent of `lsernau/grh-lean`. It verifies the elementary
algebra that converts a rank-sensitive determinant comparison into an upper
bound, and the finite-product step used after an L-function factorization.

It does not construct theta lifts, prove the determinant comparison, establish
a Dedekind-zeta factorization, or independently rebuild the GRH development.
All of those substantial inputs remain explicit hypotheses below.
-/

namespace GrhTransfer

/-- A rank-sensitive determinant comparison bounds the normalized remainder.

The common main amount `A` cancels because `n <= d` and `A >= 0`. The fraction
of useful directions is bounded below by the positive number `theta`.
-/
theorem determinant_budget
    {n d m R A E_low E_up theta : ℝ}
    (hd : 0 < d) (hm : 0 < m) (htheta : 0 < theta)
    (hrank_lower : theta * d ≤ n) (hrank_upper : n ≤ d)
    (hA : 0 ≤ A) (hlow : 0 ≤ E_low) (hup : 0 ≤ E_up)
    (hcomparison : d * (A - E_low) ≤ n * (A - m * R) + d * E_up) :
    R ≤ (E_low + E_up) / (theta * m) := by
  have hdenom : 0 < theta * m := mul_pos htheta hm
  apply (le_div_iff₀ hdenom).2
  have hbudget : n * (m * R) ≤ d * (E_low + E_up) := by
    have hdeficit : 0 ≤ (d - n) * A :=
      mul_nonneg (sub_nonneg.mpr hrank_upper) hA
    nlinarith only [hcomparison, hdeficit]
  by_cases hR : R ≤ 0
  · exact le_trans
      (mul_nonpos_of_nonpos_of_nonneg hR (le_of_lt hdenom))
      (add_nonneg hlow hup)
  · have hRpos : 0 < R := lt_of_not_ge hR
    have hscale : (theta * d) * (m * R) ≤ n * (m * R) :=
      mul_le_mul_of_nonneg_right hrank_lower (le_of_lt (mul_pos hm hRpos))
    have hscaled : d * (R * (theta * m)) ≤ d * (E_low + E_up) := by
      nlinarith only [hscale, hbudget]
    exact le_of_mul_le_mul_left hscaled hd

/-- The same conclusion when a common determinant or volume `V` lies between
the lower and upper estimates. No property of `V` beyond the two estimates
is assumed.
-/
theorem determinant_sandwich
    {n d m R A E_low E_up theta V : ℝ}
    (hd : 0 < d) (hm : 0 < m) (htheta : 0 < theta)
    (hrank_lower : theta * d ≤ n) (hrank_upper : n ≤ d)
    (hA : 0 ≤ A) (hlow : 0 ≤ E_low) (hup : 0 ≤ E_up)
    (hV_lower : d * (A - E_low) ≤ V)
    (hV_upper : V ≤ n * (A - m * R) + d * E_up) :
    R ≤ (E_low + E_up) / (theta * m) :=
  determinant_budget hd hm htheta hrank_lower hrank_upper hA hlow hup
    (le_trans hV_lower hV_upper)

/-- Sharp comparison with an index correction. The source-normalized error
`A` is not multiplied by `1/theta`; only `B + 2*I` pays that rank loss.

The theorem is slightly stronger than the nonnegative-error formulation:
`A` and the index correction `delta` may be arbitrary real numbers. Only
their displayed bounds are needed.
-/
theorem sharp_determinant_sandwich
    {n d m R M A B I theta V delta : ℝ}
    (hd : 0 < d) (hm : 0 < m) (htheta : 0 < theta)
    (hrank_lower : theta * d ≤ n) (hrank_upper : n ≤ d)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hindex : delta ≤ d * I)
    (hV_lower : d * (M - B) ≤ V + 2 * delta)
    (hV_upper : V ≤ n * (M - m * R + A)) :
    R ≤ (A + (B + 2 * I) / theta) / m := by
  have hexpand : M - m * (R - A / m) = M - m * R + A := by
    rw [mul_sub, mul_div_cancel₀ A (ne_of_gt hm)]
    ring
  have hcomparison :
      d * (M - B) ≤ n * (M - m * (R - A / m)) + d * (2 * I) := by
    rw [hexpand]
    nlinarith only [hindex, hV_lower, hV_upper]
  have hshift : R - A / m ≤ (B + 2 * I) / (theta * m) :=
    determinant_budget hd hm htheta hrank_lower hrank_upper hM hB
      (by linarith only [hI]) hcomparison
  calc
    R ≤ A / m + (B + 2 * I) / (theta * m) := by
      linarith only [hshift]
    _ = (A + (B + 2 * I) / theta) / m := by
      rw [div_mul_eq_div_div]
      exact (add_div _ _ _).symm

/-- An explicit exponent certificate: an amplification of size at least
`X ^ mu` and error at most `C * X ^ epsilon` leave exponent `epsilon - mu`.
The constant `theta` is kept visible, so rank losses cannot disappear.
-/
theorem power_scale
    {R E theta m X C epsilon mu : ℝ}
    (hX : 0 < X) (htheta : 0 < theta) (hm : 0 < m) (hC : 0 ≤ C)
    (hR : R ≤ E / (theta * m))
    (herror : E ≤ C * X ^ epsilon)
    (hamplification : X ^ mu ≤ m) :
    R ≤ (C / theta) * X ^ (epsilon - mu) := by
  have hpower : 0 < X ^ mu := Real.rpow_pos_of_pos hX mu
  have hnumerator : 0 ≤ C * X ^ epsilon :=
    mul_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hX epsilon))
  calc
    R ≤ E / (theta * m) := hR
    _ ≤ (C * X ^ epsilon) / (theta * m) :=
      div_le_div_of_nonneg_right herror (le_of_lt (mul_pos htheta hm))
    _ ≤ (C * X ^ epsilon) / (theta * X ^ mu) :=
      div_le_div_of_nonneg_left hnumerator (mul_pos htheta hpower)
        (mul_le_mul_of_nonneg_left hamplification (le_of_lt htheta))
    _ = (C / theta) * X ^ (epsilon - mu) := by
      rw [Real.rpow_sub hX, div_mul_eq_div_div]
      ring

/-- The complete elementary transfer, with all arithmetic estimates explicit.
For `mu = 1/2`, the conclusion is a square-root-scale error bound.
-/
theorem determinant_power_scale
    {n d m R A E_low E_up theta V X C epsilon mu : ℝ}
    (hd : 0 < d) (hm : 0 < m) (htheta : 0 < theta)
    (hrank_lower : theta * d ≤ n) (hrank_upper : n ≤ d)
    (hA : 0 ≤ A) (hlow : 0 ≤ E_low) (hup : 0 ≤ E_up)
    (hV_lower : d * (A - E_low) ≤ V)
    (hV_upper : V ≤ n * (A - m * R) + d * E_up)
    (hX : 0 < X) (hC : 0 ≤ C)
    (herror : E_low + E_up ≤ C * X ^ epsilon)
    (hamplification : X ^ mu ≤ m) :
    R ≤ (C / theta) * X ^ (epsilon - mu) :=
  power_scale hX htheta hm hC
    (determinant_sandwich hd hm htheta hrank_lower hrank_upper hA hlow hup
      hV_lower hV_upper)
    herror hamplification

/-- If amplification loses `delta` from the square-root exponent, that loss
appears additively in the final exponent. This equality records the exact
arithmetic rather than silently treating a positive loss as negligible.
-/
theorem square_root_loss_identity (epsilon delta : ℝ) :
    epsilon - (1 / 2 - delta) = -1 / 2 + epsilon + delta := by
  ring

/-- A finite factorization transfers the location of zeros in the open
critical strip. The factorization and each factor's zero theorem are hypotheses;
no number-field or analytic identity is proved by this lemma.
-/
theorem zeros_on_line_of_finite_factorization
    {ι : Type*} (I : Finset ι) (F : ℂ → ℂ) (L : ι → ℂ → ℂ)
    (hfactor : ∀ s : ℂ, 0 < s.re → s.re < 1 → F s = ∏ i ∈ I, L i s)
    (hline : ∀ i ∈ I, ∀ s : ℂ,
      0 < s.re → s.re < 1 → L i s = 0 → s.re = 1 / 2)
    {s : ℂ} (hzero_left : 0 < s.re) (hzero_right : s.re < 1)
    (hzero : F s = 0) :
    s.re = 1 / 2 := by
  classical
  by_contra hoffline
  have hproduct : (∏ i ∈ I, L i s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi hz =>
      hoffline (hline i hi s hzero_left hzero_right hz)
  exact hproduct ((hfactor s hzero_left hzero_right).symm.trans hzero)

#print axioms determinant_budget
#print axioms determinant_sandwich
#print axioms sharp_determinant_sandwich
#print axioms power_scale
#print axioms determinant_power_scale
#print axioms square_root_loss_identity
#print axioms zeros_on_line_of_finite_factorization

end GrhTransfer
