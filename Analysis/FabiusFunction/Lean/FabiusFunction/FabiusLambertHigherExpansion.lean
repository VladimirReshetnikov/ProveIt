import FabiusFunction.FabiusLambertPhase

/-!
# Higher-order expansion of the lower-Lambert phase

Substitution of the Lambert phase into a quadratic saddle action magnifies
phase errors by one power of `t`.  The three-term expansion with remainder
`O(1/t)` is therefore insufficient for the source's final `O(1/t)` formula.
This module retains the next `(log t - (log t)^2/2) / ((log 2)^3 t^2)` term
and proves that the remaining phase error is `O(1/t^2)`.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- Remainder after the phase expansion through order `t⁻²`. -/
noncomputable def dyadicLambertSecondRefinedRemainder (t : ℝ) : ℝ :=
  dyadicLambertRemainder t -
    Real.log t / (Real.log 2) ^ 2 / t -
    (Real.log t - Real.log t ^ 2 / 2) / (Real.log 2) ^ 3 / t ^ 2

private lemma secondRefined_eq {t : ℝ} (ht : 0 < t)
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    dyadicLambertSecondRefinedRemainder t =
      dyadicLambertRefinedRemainder t / (Real.log 2 * t) -
      (2 * (Real.log t / Real.log 2) * dyadicLambertRemainder t +
        dyadicLambertRemainder t ^ 2) / (2 * Real.log 2 * t ^ 2) +
      (Real.log (1 + dyadicLambertPerturbation t) -
        dyadicLambertPerturbation t +
        dyadicLambertPerturbation t ^ 2 / 2) / Real.log 2 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlog := dyadicLambertRemainder_eq_log_perturbation ht hsmall
  have hlog' : Real.log (1 + dyadicLambertPerturbation t) =
      Real.log 2 * dyadicLambertRemainder t := by
    rw [hlog]
    field_simp [hL]
  unfold dyadicLambertSecondRefinedRemainder dyadicLambertRefinedRemainder
  rw [hlog']
  unfold dyadicLambertPerturbation
  field_simp [hL, ht.ne']
  ring

private lemma inv_cube_isBigO_inv_sq :
    (fun t : ℝ => t⁻¹ ^ 3) =O[atTop] (fun t : ℝ => t⁻¹ ^ 2) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow,
    abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one ht)), one_mul]
  have hi : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hi0 : 0 ≤ t⁻¹ := (inv_pos.mpr (lt_of_lt_of_le zero_lt_one ht)).le
  nlinarith [sq_nonneg (t⁻¹), mul_nonneg (sq_nonneg (t⁻¹)) hi0]

private lemma log_sq_mul_inv_cube_isBigO_inv_sq :
    (fun t : ℝ => Real.log t ^ 2 * t⁻¹ ^ 3) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).isBigO.mul
    (isBigO_refl (fun t : ℝ => t⁻¹ ^ 3) atTop)
  apply h.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    simp only [id_eq]
    field_simp

private lemma log_cube_mul_inv_cube_isBigO_inv_sq :
    (fun t : ℝ => Real.log t ^ 3 * t⁻¹ ^ 3) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 3)).isBigO.mul
    (isBigO_refl (fun t : ℝ => t⁻¹ ^ 3) atTop)
  apply h.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    simp only [id_eq]
    field_simp

private lemma log_sq_mul_inv_fourth_isBigO_inv_sq :
    (fun t : ℝ => Real.log t ^ 2 * t⁻¹ ^ 4) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).isBigO.mul
    (isBigO_refl (fun t : ℝ => t⁻¹ ^ 4) atTop)
  have h' : (fun t : ℝ => Real.log t ^ 2 * t⁻¹ ^ 4) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 3) := by
    apply h.congr' Filter.EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    simp only [id_eq]
    field_simp
  exact h'.trans inv_cube_isBigO_inv_sq

private lemma remainder_isBigO_log_div :
    dyadicLambertRemainder =O[atTop] (fun t : ℝ => Real.log t * t⁻¹) := by
  have hmain : (fun t : ℝ => Real.log t / (Real.log 2) ^ 2 / t) =O[atTop]
      (fun t : ℝ => Real.log t * t⁻¹) := by
    apply (isBigO_refl (fun t : ℝ => Real.log t * t⁻¹) atTop).const_mul_left
      ((Real.log 2) ^ 2)⁻¹ |>.congr'
    · filter_upwards with t
      field_simp
    · exact Filter.EventuallyEq.rfl
  have hinv_to_log : (fun t : ℝ => 1 / t) =O[atTop]
      (fun t : ℝ => Real.log t * t⁻¹) := by
    have hone : (fun _ : ℝ => (1 : ℝ)) =O[atTop] Real.log :=
      Real.isLittleO_const_log_atTop.isBigO
    exact hone.mul (isBigO_refl (fun t : ℝ => t⁻¹) atTop) |>.congr'
      (by filter_upwards with t; simp [div_eq_mul_inv]) Filter.EventuallyEq.rfl
  apply (hmain.add (dyadicLambertRefinedRemainder_isBigO.trans hinv_to_log)).congr'
  · filter_upwards with t
    unfold dyadicLambertRefinedRemainder
    ring
  · exact Filter.EventuallyEq.rfl

private lemma perturbation_isBigO_log_div :
    dyadicLambertPerturbation =O[atTop]
      (fun t : ℝ => Real.log t * t⁻¹) := by
  unfold dyadicLambertPerturbation
  have hlog : (fun t : ℝ => Real.log t / Real.log 2) =O[atTop] Real.log :=
    ((isBigO_refl Real.log atTop).const_mul_left (Real.log 2)⁻¹).congr'
      (by filter_upwards with t; simp [div_eq_mul_inv, mul_comm])
      Filter.EventuallyEq.rfl
  have hlogDiv_to_log : (fun t : ℝ => Real.log t * t⁻¹) =O[atTop] Real.log := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul]
    exact mul_le_of_le_one_right (abs_nonneg (Real.log t))
      (by rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one ht))]
          exact inv_le_one_of_one_le₀ ht)
  have hnum := hlog.add (remainder_isBigO_log_div.trans hlogDiv_to_log)
  exact hnum.mul (isBigO_refl (fun t : ℝ => t⁻¹) atTop) |>.congr'
    (by filter_upwards with t; simp [div_eq_mul_inv]) Filter.EventuallyEq.rfl

/-- Quantitative four-term expansion of the Lambert phase.  The retained
`t⁻²` term is what is needed when the phase is substituted into a quadratic
saddle action with final error `O(1/t)`. -/
theorem dyadicLambertSecondRefinedRemainder_isBigO :
    dyadicLambertSecondRefinedRemainder =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
  let inv : ℝ → ℝ := fun t => t⁻¹
  let ell : ℝ → ℝ := Real.log
  let R : ℝ → ℝ := dyadicLambertRemainder
  let E : ℝ → ℝ := dyadicLambertRefinedRemainder
  let p : ℝ → ℝ := dyadicLambertPerturbation
  let Q : ℝ → ℝ := fun t => Real.log (1 + p t) - p t + p t ^ 2 / 2
  have hinv : (fun t : ℝ => 1 / t) =O[atTop] inv := by
    apply (isBigO_refl inv atTop).congr'
    · filter_upwards with t
      simp [inv, div_eq_mul_inv]
    · exact Filter.EventuallyEq.rfl
  have hE : E =O[atTop] inv := by
    exact dyadicLambertRefinedRemainder_isBigO.trans hinv
  have hterm1raw := hE.mul (isBigO_refl inv atTop)
  have hterm1 : (fun t : ℝ => E t / (Real.log 2 * t)) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
    exact (hterm1raw.const_mul_left (Real.log 2)⁻¹).congr'
      (by
        filter_upwards with t
        dsimp [E, inv]
        simp only [div_eq_mul_inv]
        ring)
      (by
        filter_upwards with t
        dsimp [inv]
        ring)
  have hL : ell =O[atTop] ell := isBigO_refl _ _
  have hR : R =O[atTop] (fun t => ell t * inv t) := by
    simpa [R, ell, inv] using remainder_isBigO_log_div
  have hLR := (hL.const_mul_left (Real.log 2)⁻¹).mul hR
  have hLRscaled := hLR.mul (isBigO_refl (fun t => inv t ^ 2) atTop)
  have hcross :
      (fun t => 2 * (ell t / Real.log 2) * R t * inv t ^ 2) =O[atTop]
        (fun t : ℝ => t⁻¹ ^ 2) := by
    have h := hLRscaled.const_mul_left 2
    have hraw := h.trans <| log_sq_mul_inv_cube_isBigO_inv_sq.congr_left (by
      intro t
      dsimp [ell, inv]
      ring)
    apply hraw.congr' _ Filter.EventuallyEq.rfl
    filter_upwards with t
    dsimp [ell, R, inv]
    ring
  have hR2scaled := hR.pow 2 |>.mul (isBigO_refl (fun t => inv t ^ 2) atTop)
  have hR2 : (fun t => R t ^ 2 * inv t ^ 2) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
    exact hR2scaled.trans <| log_sq_mul_inv_fourth_isBigO_inv_sq.congr_left (by
      intro t
      dsimp [ell, inv]
      ring)
  have hterm2 :
      (fun t : ℝ =>
        (2 * (Real.log t / Real.log 2) * dyadicLambertRemainder t +
          dyadicLambertRemainder t ^ 2) / (2 * Real.log 2 * t ^ 2)) =O[atTop]
        (fun t : ℝ => t⁻¹ ^ 2) := by
    have hsum := hcross.add hR2
    have hscaled := hsum.const_mul_left (2 * Real.log 2)⁻¹
    apply hscaled.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    dsimp [ell, R, inv]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', ht]
  have hQraw : Q =O[atTop] (fun t => p t ^ 3) := by
    change (fun t : ℝ => Real.log (1 + dyadicLambertPerturbation t) -
      dyadicLambertPerturbation t + dyadicLambertPerturbation t ^ 2 / 2) =O[atTop]
        (fun t : ℝ => dyadicLambertPerturbation t ^ 3)
    have hq := real_log_second_order_isBigO.comp_tendsto
      dyadicLambertPerturbation_tendsto_zero
    apply hq.congr'
    · exact Filter.Eventually.of_forall fun _ => rfl
    · exact Filter.Eventually.of_forall fun _ => rfl
  have hp : p =O[atTop] (fun t => ell t * inv t) := by
    simpa [p, ell, inv] using perturbation_isBigO_log_div
  have hp3 := hp.pow 3
  have hp3target : (fun t => p t ^ 3) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
    exact hp3.trans <| log_cube_mul_inv_cube_isBigO_inv_sq.congr_left (by
      intro t
      dsimp [ell, inv]
      ring)
  have hterm3 : (fun t => Q t / Real.log 2) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) :=
    (hQraw.trans hp3target).const_mul_left (Real.log 2)⁻¹ |>.congr'
      (by filter_upwards with t; simp [div_eq_mul_inv, mul_comm])
      Filter.EventuallyEq.rfl
  have hsum := hterm1.sub hterm2 |>.add hterm3
  apply hsum.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_dyadicLambertPhase_domain] with t ht hsmall
    rw [secondRefined_eq ht hsmall]
  · exact Filter.EventuallyEq.rfl

end Fabius
