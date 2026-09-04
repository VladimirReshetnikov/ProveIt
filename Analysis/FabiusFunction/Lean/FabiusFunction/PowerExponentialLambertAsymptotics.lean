import FabiusFunction.PowerExponentialLambertInverse
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Small-input asymptotics of scaled power--exponential Lambert phases

For a nonzero natural power `m`, positive amplitude `A`, and positive decay
rate `beta`, the profile

`A * lambda ^ m * exp (-beta * lambda)`

has two nonnegative inverse branches below its peak.  The exact inverse
geometry is provided by `PowerExponentialLambertInverse`; this module adds the
small-input analytic behavior of those branches.

The positive normalized scale

`epsilon(x) = (beta / m) * (x / A) ^ (1 / m)`

is the argument magnitude seen by both real Lambert branches.  The principal
phase is asymptotic to the elementary root `(x / A) ^ (1 / m)`.  The lower
phase diverges to positive infinity and inherits the standard two-term
`W₋₁` logarithmic expansion, stated first in the intrinsic `epsilon`
coordinate.  No assertion is made at `x = 0`, where the totalized lower branch
does not represent a finite inverse value.
-/

set_option autoImplicit false

open Filter Asymptotics Set Function
open scoped Topology

namespace Fabius

noncomputable section

/-- The positive normalized Lambert scale attached to a scaled
power--exponential profile. -/
noncomputable def powerExponentialLambertEpsilon
    (m : ℕ) (A beta x : ℝ) : ℝ :=
  beta / (m : ℝ) * (x / A) ^ ((m : ℝ)⁻¹)

/-- The normalized Lambert argument is the negative of the positive
`epsilon` scale. -/
@[simp] theorem powerExponentialLambertArgument_eq_neg_epsilon
    (m : ℕ) (A beta x : ℝ) :
    powerExponentialLambertArgument m A beta x =
      -powerExponentialLambertEpsilon m A beta x := by
  rfl

/-- The normalized Lambert scale is positive at every positive profile
value under the natural parameter hypotheses. -/
theorem powerExponentialLambertEpsilon_pos
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) (hx : 0 < x) :
    0 < powerExponentialLambertEpsilon m A beta x := by
  unfold powerExponentialLambertEpsilon
  exact mul_pos (powerExponentialInverseScale_pos hm hbeta)
    (Real.rpow_pos_of_pos (div_pos hx hA) _)

private theorem tendsto_rpow_nhdsGT_zero_of_pos
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ x ^ a) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin 0 (Ioi 0)) := by
  have hzero : Tendsto (fun x : ℝ ↦ x ^ a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop ha).comp tendsto_inv_nhdsGT_zero
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    simp only [Function.comp_apply]
    rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
    simp
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (s := Ioi 0) _ hzero
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact Real.rpow_pos_of_pos hx _

/-- The positive normalized Lambert scale tends to zero through positive
values as the profile value tends to zero from the right. -/
theorem tendsto_powerExponentialLambertEpsilon_nhdsGT_zero
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    Tendsto (powerExponentialLambertEpsilon m A beta)
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hA
  have hdiv : Tendsto (fun x : ℝ ↦ x / A)
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    have hid : Tendsto (fun x : ℝ ↦ x)
        (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := tendsto_id
    simpa only [div_eq_mul_inv, zero_mul] using
      Filter.TendstoNhdsWithinIoi.mul_const hAinv hid
  have hmpos : 0 < ((m : ℝ)⁻¹) :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  have hroot := (tendsto_rpow_nhdsGT_zero_of_pos _ hmpos).comp hdiv
  have hscale : 0 < beta / (m : ℝ) :=
    powerExponentialInverseScale_pos hm hbeta
  change Tendsto
    (fun x : ℝ ↦ beta / (m : ℝ) * (x / A) ^ ((m : ℝ)⁻¹))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0))
  convert Filter.TendstoNhdsWithinIoi.const_mul hscale hroot using 1 <;>
    simp

/-- The principal scaled phase has the elementary root as its exact first
asymptotic term at zero. -/
theorem principalPowerExponentialPhase_isEquivalent_rpow
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    (fun x : ℝ ↦ principalPowerExponentialPhase m A beta x)
      ~[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ ↦ (x / A) ^ ((m : ℝ)⁻¹)) := by
  have heps :=
    tendsto_powerExponentialLambertEpsilon_nhdsGT_zero hm hA hbeta
  have harg : Tendsto (powerExponentialLambertArgument m A beta)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := (tendsto_nhds_of_tendsto_nhdsWithin heps).neg
    have hzero : Tendsto
        (fun x : ℝ ↦ -powerExponentialLambertEpsilon m A beta x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa only [neg_zero] using h
    refine hzero.congr' <| Eventually.of_forall fun x ↦ ?_
    exact (powerExponentialLambertArgument_eq_neg_epsilon
      m A beta x).symm
  have hW := principalLambertW_isEquivalent_zero.comp_tendsto harg
  have hconst :
      (fun _ : ℝ ↦ -((m : ℝ) / beta))
        ~[nhdsWithin 0 (Ioi 0)]
      (fun _ : ℝ ↦ -((m : ℝ) / beta)) := IsEquivalent.refl
  have hscaled := hconst.mul hW
  refine (hscaled.congr_left (Eventually.of_forall fun x ↦ ?_)).congr_right
    (Eventually.of_forall fun x ↦ ?_)
  · rfl
  · simp only [Pi.mul_apply, Function.comp_apply]
    unfold powerExponentialLambertArgument
    field_simp [Nat.cast_ne_zero.mpr hm, hbeta.ne']

/-- The lower scaled phase diverges to positive infinity as the profile
value tends to zero from the right. -/
theorem tendsto_lowerPowerExponentialPhase_nhdsGT_zero_atTop
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    Tendsto (lowerPowerExponentialPhase m A beta)
      (nhdsWithin 0 (Ioi 0)) atTop := by
  have heps :=
    tendsto_powerExponentialLambertEpsilon_nhdsGT_zero hm hA hbeta
  have hW := tendsto_lowerLambertW_neg_nhdsGT_zero_atBot.comp heps
  have hscale : -((m : ℝ) / beta) < 0 :=
    neg_lt_zero.mpr (powerExponentialTurningPoint_pos hm hbeta)
  have hscaled := hW.const_mul_atBot_of_neg hscale
  exact hscaled.congr' <| Eventually.of_forall fun x ↦ by
    rfl

/-- The intrinsic two-term logarithmic main term for the lower scaled
power--exponential phase. -/
noncomputable def lowerPowerExponentialPhaseIntrinsicMain
    (m : ℕ) (A beta x : ℝ) : ℝ :=
  -((m : ℝ) / beta) *
    (Real.log (powerExponentialLambertEpsilon m A beta x) -
      Real.log |Real.log (powerExponentialLambertEpsilon m A beta x)|)

/-- The lower scaled phase inherits the standard first two terms of
`W₋₁`: after subtracting its intrinsic logarithmic main term, the
remainder tends to zero as `x ↓0`. -/
theorem lowerPowerExponentialPhase_sub_intrinsicMain_tendsto_zero
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    Tendsto
      (fun x : ℝ ↦ lowerPowerExponentialPhase m A beta x -
        lowerPowerExponentialPhaseIntrinsicMain m A beta x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have heps :=
    tendsto_powerExponentialLambertEpsilon_nhdsGT_zero hm hA hbeta
  have hrem := tendsto_lowerLambertW_expansion.comp heps
  have hscaled :
      Tendsto
        (fun x : ℝ ↦ -((m : ℝ) / beta) *
          ((lowerLambertW (-powerExponentialLambertEpsilon m A beta x) -
            (Real.log (powerExponentialLambertEpsilon m A beta x) -
              Real.log
                |Real.log (powerExponentialLambertEpsilon m A beta x)|))))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (tendsto_const_nhds.mul hrem :
        Tendsto
          (fun x : ℝ ↦ -((m : ℝ) / beta) *
            ((fun eps : ℝ ↦ lowerLambertW (-eps) -
              (Real.log eps - Real.log |Real.log eps|)) ∘
                powerExponentialLambertEpsilon m A beta) x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (-((m : ℝ) / beta) * 0)))
  exact hscaled.congr' <| Eventually.of_forall fun x ↦ by
    simp only [lowerPowerExponentialPhase,
      lowerPowerExponentialPhaseIntrinsicMain,
      powerExponentialLambertArgument_eq_neg_epsilon]
    ring

end

end Fabius
