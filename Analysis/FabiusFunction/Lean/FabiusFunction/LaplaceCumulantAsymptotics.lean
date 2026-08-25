import FabiusFunction.EndpointLaplaceComparison

/-!
# Laplace cumulants and endpoint asymptotics

This module inverts the first four cumulant polynomials for the normalized
negative-Laplace moments.  It then packages the asymptotic bookkeeping needed
by `EndpointLaplaceComparison`: logarithmic derivative bounds

`q⁽ʲ⁾(n) = O(log n / nʲ)`, for `1 ≤ j ≤ 4`,

imply the corrected endpoint/Laplace logarithmic error is `O(1/n)`.
-/

set_option autoImplicit false

open Filter Set Asymptotics
open scoped Topology

namespace Fabius

private lemma natCast_ne_zero_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≠ 0 := by
  exact_mod_cast (show n ≠ 0 by omega)

/-- Every fixed logarithmic power divided by `n²` is `O(1/n)`. -/
lemma log_pow_div_sq_isBigO_inv_nat (k : ℕ) :
    (fun n : ℕ => Real.log (n : ℝ) ^ k / (n : ℝ) ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hlog : (fun n : ℕ => Real.log (n : ℝ) ^ k) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
    convert ((Real.isLittleO_pow_log_id_atTop (n := k)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).isBigO using 1
    all_goals rfl
  have hmul := hlog.mul
    (isBigO_refl (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop)
  apply hmul.congr'
  · filter_upwards with n
    simp only [div_eq_mul_inv]
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
    field_simp

/-- The first normalized Laplace moment is the negative first logarithmic
derivative.  Together with the second-, third-, and fourth-order identities
below, this completes the Bell-polynomial inversion API through order four. -/
lemma normalizedLaplaceMoment_one_eq_logDerivatives
    (F : BoundedFabius) (s : ℝ) :
    normalizedLaplaceMoment F 1 s = -negativeLaplaceLogFirst F s := by
  unfold negativeLaplaceLogFirst
  ring

/-- The second normalized Laplace moment as a Bell polynomial in the first
two logarithmic derivatives.

This is an alias, not a second theorem.  The statement and its proof live once,
in `normalizedLaplaceMoment_two_eq_logSecond_add_first_sq`
(`FabiusFunction.EndpointLaplaceComparison`, imported by this module); the
restated copy of the identity that used to stand here has been removed, so the
two public names can no longer drift apart.  The name is kept only so that the
second-order case can be quoted under the same scheme as
`normalizedLaplaceMoment_three_eq_logDerivatives` and
`normalizedLaplaceMoment_four_eq_logDerivatives` below; new call sites should
prefer the canonical name. -/
alias normalizedLaplaceMoment_two_eq_logDerivatives :=
  normalizedLaplaceMoment_two_eq_logSecond_add_first_sq

/-- The third normalized Laplace moment as a Bell polynomial in the first
three logarithmic derivatives. -/
lemma normalizedLaplaceMoment_three_eq_logDerivatives
    (F : BoundedFabius) (s : ℝ) :
    normalizedLaplaceMoment F 3 s =
      -negativeLaplaceLogThird F s -
        3 * negativeLaplaceLogFirst F s * negativeLaplaceLogSecond F s -
          negativeLaplaceLogFirst F s ^ 3 := by
  unfold negativeLaplaceLogFirst negativeLaplaceLogSecond
    negativeLaplaceLogThird
  ring

/-- The fourth normalized Laplace moment as a Bell polynomial in the first
four logarithmic derivatives. -/
lemma normalizedLaplaceMoment_four_eq_logDerivatives
    (F : BoundedFabius) (s : ℝ) :
    normalizedLaplaceMoment F 4 s =
      negativeLaplaceLogFourth F s +
        4 * negativeLaplaceLogFirst F s * negativeLaplaceLogThird F s +
        3 * negativeLaplaceLogSecond F s ^ 2 +
        6 * negativeLaplaceLogFirst F s ^ 2 *
          negativeLaplaceLogSecond F s +
        negativeLaplaceLogFirst F s ^ 4 := by
  unfold negativeLaplaceLogFirst negativeLaplaceLogSecond
    negativeLaplaceLogThird negativeLaplaceLogFourth
  ring

/-- Bounds `q⁽ʲ⁾(n) = O(log n / nʲ)` for the first four logarithmic
derivatives discharge both moment hypotheses of the conditional endpoint
comparison, and hence give its corrected `O(1/n)` expansion. -/
theorem dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_of_logDerivative_bounds
    (F : BoundedFabius) (hF : IsFabius F)
    (hfirst :
      (fun n : ℕ => negativeLaplaceLogFirst F n) =O[atTop]
        (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)))
    (hsecond :
      (fun n : ℕ => negativeLaplaceLogSecond F n) =O[atTop]
        (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2))
    (hthird :
      (fun n : ℕ => negativeLaplaceLogThird F n) =O[atTop]
        (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 3))
    (hfourth :
      (fun n : ℕ => negativeLaplaceLogFourth F n) =O[atTop]
        (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 4)) :
    (fun n : ℕ => dyadicEndpointLaplaceLogError n +
      (n : ℝ) / 2 *
        (negativeLaplaceLogSecond F n +
          negativeLaplaceLogFirst F n ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hn : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    eventually_atTop.2 ⟨1, fun _ hn => hn⟩
  apply dyadicEndpointLaplaceLogError_add_secondOrder_isBigO F hF
  · have ht2raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      (hsecond.pow 2)
    have ht2 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          negativeLaplaceLogSecond F n ^ 2) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
      apply ht2raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have ht2' := ht2.trans (log_pow_div_sq_isBigO_inv_nat 2)
    have ht3raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      (hsecond.mul (hfirst.pow 2))
    have ht3 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          (negativeLaplaceLogSecond F n *
            negativeLaplaceLogFirst F n ^ 2)) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
      apply ht3raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have ht3' := ht3.trans (log_pow_div_sq_isBigO_inv_nat 3)
    have ht4raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      (hfirst.pow 4)
    have ht4 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          negativeLaplaceLogFirst F n ^ 4) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 4 / (n : ℝ) ^ 2) := by
      apply ht4raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have ht4' := ht4.trans (log_pow_div_sq_isBigO_inv_nat 4)
    have hsum := ht2'.add (ht3'.const_mul_left 2) |>.add ht4'
    have hscaled := hsum.const_mul_left (1 / 4 : ℝ)
    apply hscaled.congr'
    · filter_upwards with n
      ring
    · exact Filter.EventuallyEq.rfl
  · have hn3raw := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul hthird
    have hn3 :
        (fun n : ℕ => (n : ℝ) * negativeLaplaceLogThird F n) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      apply hn3raw.congr'
      · exact Filter.EventuallyEq.rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn3' := hn3.trans (by
      simpa only [pow_one] using log_pow_div_sq_isBigO_inv_nat 1)
    have hn12raw := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul
      (hfirst.mul hsecond)
    have hn12 :
        (fun n : ℕ => (n : ℝ) *
          (negativeLaplaceLogFirst F n *
            negativeLaplaceLogSecond F n)) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
      apply hn12raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn12' := hn12.trans (log_pow_div_sq_isBigO_inv_nat 2)
    have hn111raw := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul
      (hfirst.pow 3)
    have hn111 :
        (fun n : ℕ => (n : ℝ) *
          negativeLaplaceLogFirst F n ^ 3) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
      apply hn111raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn111' := hn111.trans (log_pow_div_sq_isBigO_inv_nat 3)
    have hn24raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      hfourth
    have hn24 :
        (fun n : ℕ => (n : ℝ) ^ 2 * negativeLaplaceLogFourth F n) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      apply hn24raw.congr'
      · exact Filter.EventuallyEq.rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn24' := hn24.trans (by
      simpa only [pow_one] using log_pow_div_sq_isBigO_inv_nat 1)
    have hn213raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      (hfirst.mul hthird)
    have hn213 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          (negativeLaplaceLogFirst F n *
            negativeLaplaceLogThird F n)) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
      apply hn213raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn213' := hn213.trans (log_pow_div_sq_isBigO_inv_nat 2)
    have hn222raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      (hsecond.pow 2)
    have hn222 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          negativeLaplaceLogSecond F n ^ 2) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
      apply hn222raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn222' := hn222.trans (log_pow_div_sq_isBigO_inv_nat 2)
    have hn2112raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      ((hfirst.pow 2).mul hsecond)
    have hn2112 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          (negativeLaplaceLogFirst F n ^ 2 *
            negativeLaplaceLogSecond F n)) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
      apply hn2112raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn2112' := hn2112.trans (log_pow_div_sq_isBigO_inv_nat 3)
    have hn21111raw := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul
      (hfirst.pow 4)
    have hn21111 :
        (fun n : ℕ => (n : ℝ) ^ 2 *
          negativeLaplaceLogFirst F n ^ 4) =O[atTop]
          (fun n : ℕ => Real.log (n : ℝ) ^ 4 / (n : ℝ) ^ 2) := by
      apply hn21111raw.congr'
      · filter_upwards with n
        rfl
      · filter_upwards [hn] with n hn
        have hN : (n : ℝ) ≠ 0 := natCast_ne_zero_of_one_le hn
        field_simp [hN]
    have hn21111' := hn21111.trans (log_pow_div_sq_isBigO_inv_nat 4)
    have hpoly :=
      (hn3'.const_mul_left (-1)).add (hn12'.const_mul_left (-3)) |>.add
        (hn111'.const_mul_left (-1)) |>.add hn24' |>.add
        (hn213'.const_mul_left 4) |>.add (hn222'.const_mul_left 3) |>.add
        (hn2112'.const_mul_left 6) |>.add hn21111'
    have hscaled := hpoly.const_mul_left 16
    apply hscaled.congr'
    · filter_upwards with n
      rw [normalizedLaplaceMoment_three_eq_logDerivatives,
        normalizedLaplaceMoment_four_eq_logDerivatives]
      ring
    · exact Filter.EventuallyEq.rfl

end Fabius
