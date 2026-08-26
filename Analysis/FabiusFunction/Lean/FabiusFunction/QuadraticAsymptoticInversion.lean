import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Inverting a quadratic asymptotic with its affine correction

Suppose a large parameter `lam` and an observable `T` satisfy

`T = L / 2 * lam ^ 2 - B * lam + O(log lam)`

with `L > 0`.  Completing the square and rationalizing the difference of
square roots retains the affine correction and gives

`lam = sqrt (2 * T / L) + B / L + O(log T / sqrt T)`.

The proof first obtains the intrinsic error `O(log lam / lam)`.  The
coarse equivalence `T ~ (L / 2) * lam ^ 2` then identifies that intrinsic
scale with `log T / sqrt T`.  This organization keeps the algebraic inversion
independent of monotonicity, an inverse-function theorem, or any special
function used to produce the original phase.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- The quadratic observable is asymptotic to its leading square term. -/
private theorem quadratic_main_isEquivalent
    {α : Type*} {l : Filter α} {T lam : α → ℝ} {L B : ℝ}
    (hL : 0 < L)
    (hlam : Tendsto lam l atTop)
    (hquad :
      (fun i => T i - (L / 2 * lam i ^ 2 - B * lam i)) =O[l]
        (fun i => Real.log (lam i))) :
    T ~[l] (fun i => L / 2 * lam i ^ 2) := by
  have hlinSq :
      lam =o[l] (fun i => lam i ^ 2) := by
    simpa only [pow_one] using
      (Asymptotics.isLittleO_pow_pow_atTop_of_lt
        (𝕜 := ℝ) (p := 1) (q := 2) (by norm_num)).comp_tendsto hlam
  have hlogLin :
      (fun i => Real.log (lam i)) =o[l] lam := by
    simpa only [Function.comp_apply, id_eq] using
      Real.isLittleO_log_id_atTop.comp_tendsto hlam
  have hlogSq :
      (fun i => Real.log (lam i)) =o[l] (fun i => lam i ^ 2) :=
    hlogLin.trans hlinSq
  have herr :
      (fun i => T i - (L / 2 * lam i ^ 2 - B * lam i)) =o[l]
        (fun i => lam i ^ 2) :=
    hquad.trans_isLittleO hlogSq
  have hlinear :
      (fun i => B * lam i) =o[l] (fun i => lam i ^ 2) :=
    hlinSq.const_mul_left B
  have hdiffSq :
      (fun i => T i - L / 2 * lam i ^ 2) =o[l]
        (fun i => lam i ^ 2) := by
    exact (herr.sub hlinear).congr_left fun i => by ring
  have hdiffMain :
      (fun i => T i - L / 2 * lam i ^ 2) =o[l]
        (fun i => L / 2 * lam i ^ 2) := by
    simpa only using
      hdiffSq.const_mul_right
        (div_ne_zero hL.ne' (by norm_num : (2 : ℝ) ≠ 0))
  exact hdiffMain.isEquivalent

/-- Under a positive quadratic equivalence, the intrinsic inversion rate
`log lam / lam` and the observable rate `log T / sqrt T` are Theta-equivalent. -/
private theorem log_div_sqrt_isTheta_log_div_of_isEquivalent_sq
    {α : Type*} {l : Filter α} {T lam : α → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hlam : Tendsto lam l atTop)
    (hT : T ~[l] (fun i => c * lam i ^ 2)) :
    (fun i => Real.log (T i) / Real.sqrt (T i)) =Θ[l]
      (fun i => Real.log (lam i) / lam i) := by
  have hlamSq : Tendsto (fun i => lam i ^ 2) l atTop := by
    simpa only [pow_two] using hlam.atTop_mul_atTop₀ hlam
  have hmainTop : Tendsto (fun i => c * lam i ^ 2) l atTop :=
    hlamSq.const_mul_atTop hc

  have hlogRaw :
      (fun i => Real.log (T i)) ~[l]
        (fun i => Real.log (c * lam i ^ 2)) :=
    hT.log hmainTop
  have hlogRewrite :
      (fun i => Real.log (c * lam i ^ 2)) =ᶠ[l]
        (fun i => Real.log c + 2 * Real.log (lam i)) := by
    filter_upwards [hlam.eventually_gt_atTop 0] with i hi
    rw [Real.log_mul hc.ne' (pow_ne_zero 2 hi.ne'), Real.log_pow]
    norm_num
  have htwoLogTop :
      Tendsto (fun i => 2 * Real.log (lam i)) l atTop :=
    (Real.tendsto_log_atTop.comp hlam).const_mul_atTop (by norm_num)
  have hlogMain :
      (fun i => Real.log (c * lam i ^ 2)) ~[l]
        (fun i => 2 * Real.log (lam i)) :=
    hlogRewrite.isEquivalent.trans
      ((IsEquivalent.refl (u := fun i => 2 * Real.log (lam i))).const_add_of_norm_tendsto_atTop
        (tendsto_norm_atTop_atTop.comp htwoLogTop))
  have hlog :
      (fun i => Real.log (T i)) ~[l]
        (fun i => 2 * Real.log (lam i)) :=
    hlogRaw.trans hlogMain

  have hsqrtRaw :
      (fun i => Real.sqrt (T i)) ~[l]
        (fun i => Real.sqrt (c * lam i ^ 2)) := by
    simpa only [Real.sqrt_eq_rpow] using
      IsEquivalent.rpow
        (r := (1 / 2 : ℝ))
        (fun i => mul_nonneg hc.le (sq_nonneg (lam i))) hT
  have hsqrt :
      (fun i => Real.sqrt (T i)) ~[l]
        (fun i => Real.sqrt c * lam i) := by
    apply hsqrtRaw.trans_eventuallyEq
    filter_upwards [hlam.eventually_gt_atTop 0] with i hi
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hi]

  have hrateRaw := hlog.div hsqrt
  have hrate :
      (fun i => Real.log (T i) / Real.sqrt (T i)) ~[l]
        (fun i => (2 / Real.sqrt c) *
          (Real.log (lam i) / lam i)) := by
    apply hrateRaw.congr_right
    filter_upwards with i
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hfactor : 2 / Real.sqrt c ≠ 0 :=
    div_ne_zero (by norm_num) (Real.sqrt_pos.2 hc).ne'
  exact hrate.isTheta.of_const_mul_right hfactor

/-- **Quadratic asymptotic inversion with affine correction.**

If `lam → +∞`, `L > 0`, and

`T = L / 2 * lam ^ 2 - B * lam + O(log lam)`,

then

`lam = sqrt (2 * T / L) + B / L + O(log T / sqrt T)`.

No monotonicity or nontriviality hypothesis on the source filter is required.
On the bottom filter the filter-dependent hypotheses and conclusion are
vacuous; otherwise they force `T → +∞` and all positivity needed by the
square-root argument. -/
theorem quadratic_asymptotic_inversion
    {α : Type*} {l : Filter α} {T lam : α → ℝ} {L B : ℝ}
    (hL : 0 < L)
    (hlam : Tendsto lam l atTop)
    (hquad :
      (fun i => T i - (L / 2 * lam i ^ 2 - B * lam i)) =O[l]
        (fun i => Real.log (lam i))) :
    (fun i => lam i -
        (Real.sqrt (2 * T i / L) + B / L)) =O[l]
      (fun i => Real.log (T i) / Real.sqrt (T i)) := by
  have hT : T ~[l] (fun i => L / 2 * lam i ^ 2) :=
    quadratic_main_isEquivalent hL hlam hquad
  have hTPos : ∀ᶠ i in l, 0 < T i :=
    hT.eventually_pos <| by
      filter_upwards [hlam.eventually_gt_atTop 0] with i hi
      exact mul_pos (div_pos hL (by norm_num)) (sq_pos_of_pos hi)

  have hscaledRaw :=
    (IsEquivalent.refl (u := fun _ : α => (2 / L : ℝ))).mul hT
  have hscaled :
      (fun i => 2 * T i / L) ~[l] (fun i => lam i ^ 2) := by
    refine (hscaledRaw.congr_left ?_).congr_right ?_
    · filter_upwards with i
      ring
    · filter_upwards with i
      field_simp [hL.ne'] <;> ring
  have hsqrtRaw :=
    IsEquivalent.rpow
      (r := (1 / 2 : ℝ))
      (fun i => sq_nonneg (lam i)) hscaled
  have hsqrt :
      (fun i => Real.sqrt (2 * T i / L)) ~[l] lam := by
    refine (hsqrtRaw.congr_left ?_).congr_right ?_
    · filter_upwards with i
      simp only [Real.sqrt_eq_rpow]
    · filter_upwards [hlam.eventually_gt_atTop 0] with i hi
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hi]

  have ha :
      (fun _ : α => B / L) =o[l] lam := by
    simpa only [Function.comp_apply, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop (B / L)).comp_tendsto hlam
  have hshift :
      (fun i => lam i - B / L) ~[l] lam :=
    (IsEquivalent.refl (u := lam)).sub_isLittleO ha
  have hdenDiffRaw := hshift.isLittleO.add hsqrt.isLittleO
  have hdenDiff :
      (fun i =>
        (lam i - B / L + Real.sqrt (2 * T i / L)) - 2 * lam i) =o[l]
        lam := by
    exact hdenDiffRaw.congr_left fun i => by ring
  have hden :
      (fun i => lam i - B / L + Real.sqrt (2 * T i / L)) ~[l]
        (fun i => 2 * lam i) := by
    exact (hdenDiff.const_mul_right (by norm_num : (2 : ℝ) ≠ 0)).isEquivalent
  have hdenPos :
      ∀ᶠ i in l, 0 < lam i - B / L + Real.sqrt (2 * T i / L) :=
    hden.eventually_pos <| by
      filter_upwards [hlam.eventually_gt_atTop 0] with i hi
      positivity
  have hdenInvRaw := hden.inv.isBigO
  have hdenInv :
      (fun i => (lam i - B / L + Real.sqrt (2 * T i / L))⁻¹) =O[l]
        (fun i => (lam i)⁻¹) := by
    have h := hdenInvRaw.congr_right fun i => by rw [mul_inv]
    exact h.of_const_mul_right

  have hconst :
      (fun _ : α => B ^ 2 / L ^ 2) =O[l]
        (fun i => Real.log (lam i)) := by
    simpa only [Function.comp_apply] using
      ((Real.isLittleO_const_log_atTop
        (c := B ^ 2 / L ^ 2)).comp_tendsto hlam).isBigO
  have hnumRaw := hconst.add (hquad.const_mul_left (-2 / L))
  have hnum :
      (fun i =>
        (lam i - B / L) ^ 2 -
          (Real.sqrt (2 * T i / L)) ^ 2) =O[l]
        (fun i => Real.log (lam i)) := by
    apply hnumRaw.congr'
    · filter_upwards [hTPos] with i hTi
      rw [Real.sq_sqrt (div_nonneg
        (mul_nonneg (by norm_num) hTi.le) hL.le)]
      field_simp [hL.ne'] <;> ring
    · exact Filter.EventuallyEq.rfl

  have hproduct := hnum.mul hdenInv
  have hstrong :
      (fun i => lam i -
          (Real.sqrt (2 * T i / L) + B / L)) =O[l]
        (fun i => Real.log (lam i) / lam i) := by
    apply hproduct.congr'
    · filter_upwards [hdenPos] with i hdi
      field_simp [hdi.ne', hL.ne'] <;> ring
    · filter_upwards with i
      simp only [div_eq_mul_inv]

  have hrate :=
    log_div_sqrt_isTheta_log_div_of_isEquivalent_sq
      (c := L / 2) (div_pos hL (by norm_num)) hlam hT
  exact hstrong.trans_isTheta hrate.symm

end Fabius
