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

/-- **Products multiply the log/power exponents**: `f = O(logᵃ¹/nʲ¹)` and
`g = O(logᵃ²/nʲ²)` give `fg = O(log^{a₁+a₂}/n^{j₁+j₂})`.  This is the
bookkeeping step that every cumulant term of
`dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_of_logDerivative_bounds`
performs. -/
theorem isBigO_log_pow_div_pow_mul {f g : ℕ → ℝ} {a₁ j₁ a₂ j₂ : ℕ}
    (hf : f =O[atTop] fun n : ℕ => Real.log (n : ℝ) ^ a₁ / (n : ℝ) ^ j₁)
    (hg : g =O[atTop] fun n : ℕ => Real.log (n : ℝ) ^ a₂ / (n : ℝ) ^ j₂) :
    (fun n : ℕ => f n * g n) =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) ^ (a₁ + a₂) / (n : ℝ) ^ (j₁ + j₂) :=
  (hf.mul hg).congr_right fun n => by
    rw [pow_add, pow_add, div_mul_div_comm]

/-- The `m`-fold power case of `isBigO_log_pow_div_pow_mul`. -/
theorem isBigO_log_pow_div_pow_pow {f : ℕ → ℝ} {a j : ℕ} (m : ℕ)
    (hf : f =O[atTop] fun n : ℕ => Real.log (n : ℝ) ^ a / (n : ℝ) ^ j) :
    (fun n : ℕ => f n ^ m) =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) ^ (a * m) / (n : ℝ) ^ (j * m) :=
  (hf.pow m).congr_right fun n => by
    rw [div_pow, ← pow_mul, ← pow_mul]

/-- **The polynomial-weight step**: a bound `f = O(logᵃ/nʲ)` survives
multiplication by `nᵏ` as `O(1/n)` whenever `k + 2 ≤ j`, because the two
spare powers of `n` absorb every power of the logarithm
(`log_pow_div_sq_isBigO_inv_nat`).  Each of the eleven cumulant terms below
is one application. -/
theorem isBigO_natCast_pow_mul_of_isBigO_log_pow_div {f : ℕ → ℝ} {k a j : ℕ}
    (hj : k + 2 ≤ j)
    (hf : f =O[atTop] fun n : ℕ => Real.log (n : ℝ) ^ a / (n : ℝ) ^ j) :
    (fun n : ℕ => (n : ℝ) ^ k * f n) =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  have hstep :
      (fun n : ℕ => (n : ℝ) ^ k * (Real.log (n : ℝ) ^ a / (n : ℝ) ^ j))
        =O[atTop] fun n : ℕ => Real.log (n : ℝ) ^ a / (n : ℝ) ^ 2 := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_atTop.2 ⟨1, fun (_ : ℕ) hn => hn⟩] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hkey : (n : ℝ) ^ k / (n : ℝ) ^ j ≤ 1 / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
      exact pow_le_pow_right₀ hn1 (by omega)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    calc (n : ℝ) ^ k * (Real.log (n : ℝ) ^ a / (n : ℝ) ^ j)
        = Real.log (n : ℝ) ^ a * ((n : ℝ) ^ k / (n : ℝ) ^ j) := by ring
      _ ≤ Real.log (n : ℝ) ^ a * (1 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = Real.log (n : ℝ) ^ a / (n : ℝ) ^ 2 := by ring
  exact ((isBigO_refl (fun n : ℕ => (n : ℝ) ^ k) atTop).mul hf).trans
    (hstep.trans (log_pow_div_sq_isBigO_inv_nat a))

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
  -- normalise the four hypotheses to the `logᵃ/nʲ` shape
  have h1 : (fun n : ℕ => negativeLaplaceLogFirst F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ 1 / (n : ℝ) ^ 1) := by
    simpa only [pow_one] using hfirst
  have h2 : (fun n : ℕ => negativeLaplaceLogSecond F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ 1 / (n : ℝ) ^ 2) := by
    simpa only [pow_one] using hsecond
  have h3 : (fun n : ℕ => negativeLaplaceLogThird F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ 1 / (n : ℝ) ^ 3) := by
    simpa only [pow_one] using hthird
  have h4 : (fun n : ℕ => negativeLaplaceLogFourth F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ 1 / (n : ℝ) ^ 4) := by
    simpa only [pow_one] using hfourth
  apply dyadicEndpointLaplaceLogError_add_secondOrder_isBigO F hF
  · -- the squared second-order term
    have ht2' : (fun n : ℕ =>
        (n : ℝ) ^ 2 * negativeLaplaceLogSecond F n ^ 2) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_pow 2 h2)
    have ht3' : (fun n : ℕ => (n : ℝ) ^ 2 *
        (negativeLaplaceLogSecond F n *
          negativeLaplaceLogFirst F n ^ 2)) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_mul h2 (isBigO_log_pow_div_pow_pow 2 h1))
    have ht4' : (fun n : ℕ =>
        (n : ℝ) ^ 2 * negativeLaplaceLogFirst F n ^ 4) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_pow 4 h1)
    have hsum := ht2'.add (ht3'.const_mul_left 2) |>.add ht4'
    have hscaled := hsum.const_mul_left (1 / 4 : ℝ)
    apply hscaled.congr'
    · filter_upwards with n
      ring
    · exact Filter.EventuallyEq.rfl
  · -- the third- and fourth-moment transfer term
    have hn3' : (fun n : ℕ =>
        (n : ℝ) ^ 1 * negativeLaplaceLogThird F n) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega) h3
    have hn12' : (fun n : ℕ => (n : ℝ) ^ 1 *
        (negativeLaplaceLogFirst F n *
          negativeLaplaceLogSecond F n)) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_mul h1 h2)
    have hn111' : (fun n : ℕ =>
        (n : ℝ) ^ 1 * negativeLaplaceLogFirst F n ^ 3) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_pow 3 h1)
    have hn24' : (fun n : ℕ =>
        (n : ℝ) ^ 2 * negativeLaplaceLogFourth F n) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega) h4
    have hn213' : (fun n : ℕ => (n : ℝ) ^ 2 *
        (negativeLaplaceLogFirst F n *
          negativeLaplaceLogThird F n)) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_mul h1 h3)
    have hn222' : (fun n : ℕ =>
        (n : ℝ) ^ 2 * negativeLaplaceLogSecond F n ^ 2) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_pow 2 h2)
    have hn2112' : (fun n : ℕ => (n : ℝ) ^ 2 *
        (negativeLaplaceLogFirst F n ^ 2 *
          negativeLaplaceLogSecond F n)) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_mul (isBigO_log_pow_div_pow_pow 2 h1) h2)
    have hn21111' : (fun n : ℕ =>
        (n : ℝ) ^ 2 * negativeLaplaceLogFirst F n ^ 4) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) :=
      isBigO_natCast_pow_mul_of_isBigO_log_pow_div (by omega)
        (isBigO_log_pow_div_pow_pow 4 h1)
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
