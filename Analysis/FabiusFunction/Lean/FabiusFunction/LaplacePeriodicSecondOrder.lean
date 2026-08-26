import FabiusFunction.NegativeLaplaceDerivativeBounds
import FabiusFunction.PeriodicRegularity
import FabiusFunction.LaplaceCumulantAsymptotics
import FabiusFunction.FabiusDyadicSharpCumulant

/-!
# Periodic expansion of the second endpoint cumulant

This module differentiates the exact quadratic-plus-periodic decomposition of
the negative-Laplace logarithm and controls its forward-tail derivative. It
proves, on the full positive real ray,

`q'(s) = (-log s / log 2 + 1/2 + Ψ'(logb 2 s) / log 2) / s + O(s⁻²)`

and records the natural-number sampling used below. It then combines this with
the sharper second-derivative estimate

`q''(n) = log n / (log 2 * n²) + O(n⁻²)`.

The linear logarithmic terms cancel in `n (q'' + (q')²) / 2`, yielding the
explicit periodic-derivative expansion of the endpoint cumulant with an
`O(1/n)` error. The final theorem inserts this expansion into the
unconditional sharp dyadic Fabius asymptotic.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

private lemma norm_negativeLaplaceForwardTermFirst_le_invSq_geometric
    {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermFirst s n‖ ≤
      (4 / s ^ 2) * (1 / 2 : ℝ) ^ n := by
  let a : ℝ := (2 : ℝ) ^ n
  let y : ℝ := s * a
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 1 ≤ y := by
    dsimp [y]
    have ha1 : 1 ≤ a := one_le_pow₀ (by norm_num)
    nlinarith
  have he : Real.exp (-y) ≤ 1 / 2 := by
    calc
      Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le
  have hden : 0 < 1 - Real.exp (-y) := by linarith
  have hfrac := exp_neg_div_one_sub_pow_le 1 hy
  norm_num at hfrac
  have hpow := pow_mul_exp_neg_le_factorial 2 (le_trans (by norm_num) hy)
  norm_num at hpow
  unfold negativeLaplaceForwardTermFirst
  change ‖a * Real.exp (-y) / (1 - Real.exp (-y))‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (mul_pos ha (Real.exp_pos _)) hden)]
  calc
    a * Real.exp (-y) / (1 - Real.exp (-y)) =
        a * (Real.exp (-y) / (1 - Real.exp (-y))) := by ring
    _ ≤ a * (2 * Real.exp (-y)) := by gcongr
    _ ≤ (4 / s ^ 2) * (1 / 2 : ℝ) ^ n := by
      have hpow2 : 2 * (a * (2 * Real.exp (-y))) * (s ^ 2 * a) ≤
          2 * 4 := by
        dsimp [y] at hpow
        nlinarith
      have hgeom : (1 / 2 : ℝ) ^ n = 1 / a := by
        dsimp [a]
        rw [one_div_pow]
      rw [hgeom]
      rw [show 4 / s ^ 2 * (1 / a) = 4 / (s ^ 2 * a) by
        field_simp]
      rw [le_div_iff₀ (mul_pos (sq_pos_of_pos hs0) ha)]
      nlinarith

/-- Explicit bound on the forward tail of the first derivative series: for
`1 ≤ s`, `‖negativeLaplaceForwardTailFirst s‖ ≤ 8 / s ^ 2`.  Proved by summing
a geometric majorant of the individual terms.  Besides the `O(s⁻²)` estimate
below, it is used by `abs_mul_negativeLaplaceForwardTailFirst_le_eight` in
`FabiusLambertDerivativeBounds`. -/
theorem norm_negativeLaplaceForwardTailFirst_le_inv_sq
    {s : ℝ} (hs : 1 ≤ s) :
    ‖negativeLaplaceForwardTailFirst s‖ ≤ 8 / s ^ 2 := by
  have hgeom : Summable (fun n : ℕ => (4 / s ^ 2) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hterm : Summable (negativeLaplaceForwardTermFirst s) :=
    hgeom.of_norm_bounded (fun n => norm_negativeLaplaceForwardTermFirst_le_invSq_geometric hs n)
  calc
    ‖negativeLaplaceForwardTailFirst s‖ ≤ ∑' n : ℕ, ‖negativeLaplaceForwardTermFirst s n‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ ≤ ∑' n : ℕ, (4 / s ^ 2) * (1 / 2 : ℝ) ^ n := by
      exact hterm.norm.tsum_le_tsum
        (fun n => norm_negativeLaplaceForwardTermFirst_le_invSq_geometric hs n) hgeom
    _ = 8 / s ^ 2 := by
      rw [tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      ring

/-- The derivative of the forward tail is `O(s⁻²)` on the full real
positive ray. -/
theorem negativeLaplaceForwardTailFirst_isBigO_inv_sq_real :
    (fun s : ℝ => negativeLaplaceForwardTailFirst s) =O[atTop]
      (fun s : ℝ => (s ^ 2)⁻¹) := by
  apply IsBigO.of_bound 8
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have h := norm_negativeLaplaceForwardTailFirst_le_inv_sq hs
  calc
    ‖negativeLaplaceForwardTailFirst s‖ ≤ 8 / s ^ 2 := h
    _ = 8 * ‖(s ^ 2)⁻¹‖ := by
      rw [div_eq_mul_inv, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (s ^ 2)⁻¹)]

/-- Natural-number sampling of the real positive-ray tail estimate. -/
theorem negativeLaplaceForwardTailFirst_isBigO_inv_sq_nat :
    (fun n : ℕ => negativeLaplaceForwardTailFirst n) =O[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa using negativeLaplaceForwardTailFirst_isBigO_inv_sq_real.natCast_atTop

/-- Hypothesis-carrying form of the periodic expansion of the first
logarithmic derivative.  For `0 < s`, assuming `negativeLaplacePsi` is
differentiable at `Real.logb 2 s` and `negativeLaplaceForwardTail` at `s`,
`negativeLaplaceLogFirst F s` equals
`(-log s / log 2 + 1 / 2 + deriv negativeLaplacePsi (logb 2 s) / log 2) / s`
minus `deriv negativeLaplaceForwardTail s`.  Requires `IsFabius F`.  It is
used to prove `negativeLaplaceLogFirst_eq_periodic` just below. -/
theorem negativeLaplaceLogFirst_eq_periodic_of_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s)
    (hpsi : HasDerivAt negativeLaplacePsi
      (deriv negativeLaplacePsi (Real.logb 2 s)) (Real.logb 2 s))
    (htail : HasDerivAt negativeLaplaceForwardTail
      (deriv negativeLaplaceForwardTail s) s) :
    negativeLaplaceLogFirst F s =
      (-Real.log s / Real.log 2 + 1 / 2 +
          deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2) / s -
        deriv negativeLaplaceForwardTail s := by
  have hlog := Real.hasDerivAt_log hs.ne'
  have hlogb : HasDerivAt (fun x : ℝ => Real.logb 2 x)
      ((1 / s) / Real.log 2) s := by
    unfold Real.logb
    simpa [one_div] using hlog.div_const (Real.log 2)
  have hperiodic := hpsi.comp s hlogb
  have hquad := ((hlog.pow 2).neg.div_const (2 * Real.log 2)).add
    (hlog.div_const 2)
  have hrhs := (hquad.add (hasDerivAt_const s negativeLaplacePeriodicMean) |>.add
    hperiodic).sub htail
  let rhs : ℝ → ℝ := fun x =>
    -(Real.log x) ^ 2 / (2 * Real.log 2) + Real.log x / 2 +
      negativeLaplacePeriodicMean + negativeLaplacePsi (Real.logb 2 x) -
        negativeLaplaceForwardTail x
  have hrhs' := hrhs.congr_of_eventuallyEq
    (show rhs =ᶠ[nhds s] _ by
      filter_upwards with x
      dsimp only [rhs, Function.comp_apply, Pi.add_apply, Pi.sub_apply,
        Pi.neg_apply, Pi.pow_apply])
  have heq : negativeLaplaceLog =ᶠ[nhds s] rhs := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [negativeLaplaceLog_exact_periodic_decomposition x hx]
    dsimp only [rhs]
    unfold negativeLaplacePsi negativeLaplaceTailError
    ring
  have hneg := hrhs'.congr_of_eventuallyEq heq
  have hu := (negativeLaplaceLog_hasDerivAt F hF hs).unique hneg
  norm_num at hu
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hs.ne'] at hu ⊢
  linear_combination hu

/-- Exact first-derivative form of the quadratic-plus-periodic Laplace
decomposition. -/
theorem negativeLaplaceLogFirst_eq_periodic
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    negativeLaplaceLogFirst F s =
      (-Real.log s / Real.log 2 + 1 / 2 +
          deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2) / s -
        negativeLaplaceForwardTailFirst s := by
  have ht := negativeLaplaceForwardTail_hasDerivAt s hs
  have h := negativeLaplaceLogFirst_eq_periodic_of_hasDerivAt F hF hs
    (negativeLaplacePsi_hasDerivAt _) ht.differentiableAt.hasDerivAt
  rwa [ht.deriv] at h

/-- On the full positive real ray, the first logarithmic derivative differs
from its periodic main term by `O(s⁻²)`. The error is exactly the negative
derivative of the exponentially small forward tail. -/
theorem negativeLaplaceLogFirst_sub_periodic_main_isBigO_inv_sq_real
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun s : ℝ => negativeLaplaceLogFirst F s -
      ((-Real.log s / Real.log 2 + 1 / 2 +
          deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2) / s)) =O[atTop]
      (fun s : ℝ => (s ^ 2)⁻¹) := by
  have htail := negativeLaplaceForwardTailFirst_isBigO_inv_sq_real
  apply (htail.const_mul_left (-1)).congr'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    rw [negativeLaplaceLogFirst_eq_periodic F hF (zero_lt_one.trans_le hs)]
    ring
  · exact Filter.EventuallyEq.rfl

/-- Natural-number sampling of the real positive-ray first-derivative
approximation. -/
theorem negativeLaplaceLogFirst_sub_periodic_main_isBigO_inv_sq_nat
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => negativeLaplaceLogFirst F n -
      ((-Real.log (n : ℝ) / Real.log 2 + 1 / 2 +
          deriv negativeLaplacePsi (Real.logb 2 n) / Real.log 2) /
        (n : ℝ))) =O[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  simpa using
    (negativeLaplaceLogFirst_sub_periodic_main_isBigO_inv_sq_real F hF).natCast_atTop


private lemma one_isBigO_log_nat :
    (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  apply IsBigO.of_bound (1 / Real.log 2)
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hn0 (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))]
  rw [div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos (by norm_num))]
  nlinarith

private lemma nat_mul_inv_sq_isBigO_inv :
    (fun n : ℕ => (n : ℝ) * ((n : ℝ) ^ 2)⁻¹) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).congr'
  · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  · exact Filter.EventuallyEq.rfl

private lemma nat_mul_inv_sq_sq_isBigO_inv :
    (fun n : ℕ => (n : ℝ) * (((n : ℝ) ^ 2)⁻¹) ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (inv_pos.mpr hn0)]
  rw [show (n : ℝ) * (((n : ℝ) ^ 2)⁻¹) ^ 2 = ((n : ℝ) ^ 3)⁻¹ by
    field_simp]
  norm_num
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  exact inv_anti₀ (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_left hsq hn0.le])

/-- Algebraic transfer from sharp first- and second-log-derivative
approximations to the periodic second-order endpoint term. -/
theorem dyadicEndpointSecondOrder_sub_periodicMain_isBigO_of_bounds
    (F : BoundedFabius) (d : ℕ → ℝ)
    (hd : d =O[atTop] (fun _ : ℕ => (1 : ℝ)))
    (hfirst :
      (fun n : ℕ => negativeLaplaceLogFirst F n -
        ((-Real.log (n : ℝ) / Real.log 2 + 1 / 2 + d n / Real.log 2) /
          (n : ℝ))) =O[atTop]
        (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹))
    (hsecond :
      (fun n : ℕ => negativeLaplaceLogSecond F n -
        Real.log (n : ℝ) / (Real.log 2 * (n : ℝ) ^ 2)) =O[atTop]
        (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)) :
    (fun n : ℕ => dyadicEndpointSecondOrder F n -
      (Real.log (n : ℝ) ^ 2 /
          (2 * (Real.log 2) ^ 2 * (n : ℝ)) -
        Real.log (n : ℝ) / ((Real.log 2) ^ 2 * (n : ℝ)) * d n)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  let ell : ℕ → ℝ := fun n => Real.log (n : ℝ)
  let invSq : ℕ → ℝ := fun n => ((n : ℝ) ^ 2)⁻¹
  let u : ℕ → ℝ := fun n => -ell n / Real.log 2 + 1 / 2 + d n / Real.log 2
  let e₁ : ℕ → ℝ := fun n =>
    negativeLaplaceLogFirst F n - u n / (n : ℝ)
  let e₂ : ℕ → ℝ := fun n =>
    negativeLaplaceLogSecond F n - ell n / (Real.log 2 * (n : ℝ) ^ 2)
  have he₁ : e₁ =O[atTop] invSq := by simpa [e₁, u, ell, invSq] using hfirst
  have he₂ : e₂ =O[atTop] invSq := by simpa [e₂, ell, invSq] using hsecond
  have hell : ell =O[atTop] ell := isBigO_refl _ _
  have hconst : (fun _ : ℕ => (1 : ℝ)) =O[atTop] ell := by
    simpa [ell] using one_isBigO_log_nat
  have hdell : d =O[atTop] ell := hd.trans hconst
  have hu : u =O[atTop] ell := by
    dsimp [u]
    exact ((hell.const_mul_left (-(Real.log 2)⁻¹)).add
      (hconst.const_mul_left (1 / 2))).add
        (hdell.const_mul_left (Real.log 2)⁻¹) |>.congr' (by
          filter_upwards with n
          dsimp [ell]
          ring) Filter.EventuallyEq.rfl
  have hcrossRaw := hu.mul he₁
  have hcross : (fun n => u n * e₁ n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
    have hh : (fun n => ell n * invSq n) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) := by
      simpa only [ell, invSq, pow_one, div_eq_mul_inv] using
        (log_pow_div_sq_isBigO_inv_nat 1)
    exact hcrossRaw.trans hh
  have he₂scaledRaw := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul he₂
  have he₂scaled : (fun n : ℕ => (n : ℝ) * e₂ n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
    he₂scaledRaw.trans nat_mul_inv_sq_isBigO_inv
  have he₁sqRaw := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul (he₁.pow 2)
  have he₁sq : (fun n : ℕ => (n : ℝ) * e₁ n ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
    he₁sqRaw.trans nat_mul_inv_sq_sq_isBigO_inv
  have hdres : (fun n => d n ^ 2 / (Real.log 2) ^ 2 +
      d n / Real.log 2 + 1 / 4) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    have hone := isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop
    have hd2 : (fun n => d n ^ 2) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
      simpa using hd.pow 2
    simpa [div_eq_mul_inv, mul_comm] using
      ((hd2.const_mul_left ((Real.log 2) ^ 2)⁻¹).add
      (hd.const_mul_left (Real.log 2)⁻¹)).add
        (hone.const_mul_left (1 / 4))
  have hdresScaledRaw := hdres.mul
    (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop)
  have hdresScaled : (fun n =>
      (d n ^ 2 / (Real.log 2) ^ 2 + d n / Real.log 2 + 1 / 4) *
        (n : ℝ)⁻¹) =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa using hdresScaledRaw
  have hsum := (he₂scaled.const_mul_left (1 / 2)).add hcross |>.add
      (he₁sq.const_mul_left (1 / 2)) |>.add
        (hdresScaled.const_mul_left (1 / 2))
  apply hsum.congr'
  · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp [e₁, e₂, u, ell, dyadicEndpointSecondOrder]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hn0]
    ring
  · exact Filter.EventuallyEq.rfl

/-- A globally bounded periodic derivative stays `O(1)` after composition with
an arbitrary phase map and along an arbitrary filter. -/
theorem deriv_negativeLaplacePsi_comp_isBigO_one
    {α : Type*} (l : Filter α) (phase : α → ℝ) :
    (fun x => deriv negativeLaplacePsi (phase x)) =O[l]
      (fun _ : α => (1 : ℝ)) := by
  rcases (Metric.isBounded_iff_subset_closedBall 0).mp
      isBounded_range_deriv_negativeLaplacePsi with ⟨C, hC⟩
  apply IsBigO.of_bound C
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
  simpa [Metric.mem_closedBall, Real.dist_eq] using
    hC (Set.mem_range_self (phase x))

/-- Boundedness of the periodic derivative remains uniform after sampling it
at the logarithmic phases of the natural numbers. -/
theorem deriv_negativeLaplacePsi_logb_isBigO_one_nat :
    (fun n : ℕ => deriv negativeLaplacePsi (Real.logb 2 n)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  exact deriv_negativeLaplacePsi_comp_isBigO_one atTop
    (fun n : ℕ => Real.logb 2 n)

/-- The second endpoint cumulant equals its logarithmic-square and periodic
phase main terms up to `O(1/n)`.  The linear logarithmic term from `q''`
cancels exactly against the constant cross-term in `(q')²`. -/
theorem dyadicEndpointSecondOrder_sub_periodicMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => dyadicEndpointSecondOrder F n -
      (Real.log (n : ℝ) ^ 2 /
          (2 * (Real.log 2) ^ 2 * (n : ℝ)) -
        Real.log (n : ℝ) / ((Real.log 2) ^ 2 * (n : ℝ)) *
          deriv negativeLaplacePsi (Real.logb 2 n))) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact dyadicEndpointSecondOrder_sub_periodicMain_isBigO_of_bounds F
    (fun n : ℕ => deriv negativeLaplacePsi (Real.logb 2 n))
    deriv_negativeLaplacePsi_logb_isBigO_one_nat
    (negativeLaplaceLogFirst_sub_periodic_main_isBigO_inv_sq_nat F hF)
    (negativeLaplaceLogSecond_sub_log_main_isBigO_inv_sq_nat F hF)

/-- Sharp dyadic main term after replacing the exact endpoint cumulant by its
explicit logarithmic-square and periodic-derivative expansion. -/
noncomputable def dyadicSharpPeriodicDerivativeMain (n : ℕ) : ℝ :=
  dyadicSharpElementaryMain n + fabiusSharpAsymptoticConstant +
    negativeLaplacePsi (Real.logb 2 n) -
      (Real.log (n : ℝ) ^ 2 /
          (2 * (Real.log 2) ^ 2 * (n : ℝ)) -
        Real.log (n : ℝ) / ((Real.log 2) ^ 2 * (n : ℝ)) *
          deriv negativeLaplacePsi (Real.logb 2 n))

/-- Unconditional sharp dyadic asymptotic with the endpoint cumulant replaced
by the explicit periodic-derivative main term. -/
theorem log_fabius_dyadic_sub_periodicDerivativeMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ =>
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpPeriodicDerivativeMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have h := (log_fabius_dyadic_sub_explicitCumulantMain_isBigO F hF).sub
    (dyadicEndpointSecondOrder_sub_periodicMain_isBigO F hF)
  apply h.congr'
  · filter_upwards with n
    unfold dyadicSharpExplicitCumulantMain dyadicSharpPeriodicDerivativeMain
    ring
  · exact Filter.EventuallyEq.rfl

end Fabius
