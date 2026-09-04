import FabiusFunction.PowerExponentialLambert
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Calculus of scaled power--exponential Lambert phases

This module adds the smooth-interior calculus and order structure of the two
inverse branches defined in `PowerExponentialLambert.lean`.  For nonzero
natural power `m`, positive amplitude `A`, and positive rate `beta`, the
principal phase is strictly increasing from zero toward `m / beta`, while
the lower phase is strictly decreasing above `m / beta`.

The two phases are continuous on their full natural profile-value domains:
the principal branch on the closed interval from zero through the peak and
the lower branch on the positive half-open interval through the peak.  Their
derivative formulas below remain restricted to the smooth interior.

The derivative formula is the inverse derivative of

`lambda ↦ A * lambda ^ m * exp (-beta * lambda)`:

`lambda'(x) = lambda(x) / (x * (m - beta * lambda(x)))`.

It is asserted only for `0 < x < powerExponentialPeak m A beta`; the common
turning point is excluded because the inverse derivative is singular there.
The formula is proved once, for an arbitrary real Lambert branch `W`
satisfying the inverse-derivative law and the defining equation at the
normalized argument (`powerExponentialPhase_hasDerivAt_of_branch`); the
two concrete phases are instances.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-- The principal phase lies strictly above zero in the smooth interior. -/
theorem principalPowerExponentialPhase_pos
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    0 < principalPowerExponentialPhase m A beta x := by
  have harg := powerExponentialLambertArgument_mem_Ioo hm hA hbeta hx
  have hW : principalLambertW
      (powerExponentialLambertArgument m A beta x) < 0 := by
    have hmono := principalLambertW_strictMonoOn
      (mem_Ici.mpr harg.1.le)
      (mem_Ici.mpr (neg_nonpos.mpr (Real.exp_pos _).le)) harg.2
    simpa only [principalLambertW_zero] using hmono
  unfold principalPowerExponentialPhase
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos (div_pos
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta)) hW

/-- The principal phase stays strictly below the turning point on the smooth
interior. -/
theorem principalPowerExponentialPhase_lt_turningPoint
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    principalPowerExponentialPhase m A beta x < (m : ℝ) / beta := by
  have harg := powerExponentialLambertArgument_mem_Ioo hm hA hbeta hx
  have hW := neg_one_lt_principalLambertW harg.1
  have hscale : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  unfold principalPowerExponentialPhase
  nlinarith

/-- The lower phase stays strictly beyond the turning point on the smooth
interior. -/
theorem turningPoint_lt_lowerPowerExponentialPhase
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    (m : ℝ) / beta < lowerPowerExponentialPhase m A beta x := by
  have harg := powerExponentialLambertArgument_mem_Ioo hm hA hbeta hx
  have hW := lowerLambertW_lt_neg_one harg
  have hscale : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  unfold lowerPowerExponentialPhase
  nlinarith

/-- The principal phase maps the closed input interval into the lower side
of the profile turning point. -/
theorem principalPowerExponentialPhase_mem_Icc
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Icc 0 (powerExponentialPeak m A beta)) :
    principalPowerExponentialPhase m A beta x ∈
      Icc 0 ((m : ℝ) / beta) := by
  have harg := powerExponentialLambertArgument_mem_Icc hm hA hbeta hx
  have hWlo := neg_one_le_principalLambertW harg.1
  have hWhi : principalLambertW
      (powerExponentialLambertArgument m A beta x) ≤ 0 := by
    have h := principalLambertW_strictMonoOn.monotoneOn
      (mem_Ici.mpr harg.1)
      (mem_Ici.mpr (neg_nonpos.mpr (Real.exp_pos _).le)) harg.2
    simpa only [principalLambertW_zero] using h
  have hscale : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  unfold principalPowerExponentialPhase
  constructor <;> nlinarith

/-- The principal phase maps the open input interval into the open lower
side of the turning point. -/
theorem principalPowerExponentialPhase_mem_Ioo
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    principalPowerExponentialPhase m A beta x ∈
      Ioo 0 ((m : ℝ) / beta) :=
  ⟨principalPowerExponentialPhase_pos hm hA hbeta hx,
    principalPowerExponentialPhase_lt_turningPoint hm hA hbeta hx⟩

/-- The lower phase maps its endpoint-inclusive positive input interval to
the upper side of the profile turning point. -/
theorem lowerPowerExponentialPhase_mem_Ici
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioc 0 (powerExponentialPeak m A beta)) :
    lowerPowerExponentialPhase m A beta x ∈ Ici ((m : ℝ) / beta) := by
  have harg := powerExponentialLambertArgument_mem_Ico hm hA hbeta hx
  have hW := lowerLambertW_le_neg_one harg
  have hscale : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  unfold lowerPowerExponentialPhase
  calc
    (m : ℝ) / beta = (-((m : ℝ) / beta)) * (-1) := by ring
    _ ≤ (-((m : ℝ) / beta)) *
        lowerLambertW (powerExponentialLambertArgument m A beta x) :=
      mul_le_mul_of_nonpos_left hW (neg_nonpos.mpr hscale.le)

/-- The lower phase lies strictly beyond the turning point for inputs
strictly below the profile peak. -/
theorem lowerPowerExponentialPhase_mem_Ioi
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    lowerPowerExponentialPhase m A beta x ∈ Ioi ((m : ℝ) / beta) :=
  turningPoint_lt_lowerPowerExponentialPhase hm hA hbeta hx

/-- Derivative of the normalized Lambert argument at every positive input. -/
theorem powerExponentialLambertArgument_hasDerivAt
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hx : 0 < x) :
    HasDerivAt (powerExponentialLambertArgument m A beta)
      (powerExponentialLambertArgument m A beta x /
        ((m : ℝ) * x)) x := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hA0 : A ≠ 0 := hA.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hratio0 : x / A ≠ 0 := div_ne_zero hx0 hA0
  have hlin : HasDerivAt (fun y : ℝ ↦ y / A) (1 / A) x := by
    simpa only [id_eq, one_div] using (hasDerivAt_id x).div_const A
  have hpow := hlin.rpow_const (p := (m : ℝ)⁻¹) (Or.inl hratio0)
  have hraw := (hpow.const_mul (beta / (m : ℝ))).neg
  change HasDerivAt
    (-fun y : ℝ ↦ beta / (m : ℝ) * (y / A) ^ ((m : ℝ)⁻¹))
      (powerExponentialLambertArgument m A beta x /
        ((m : ℝ) * x)) x
  refine hraw.congr_deriv ?_
  rw [Real.rpow_sub_one hratio0]
  unfold powerExponentialLambertArgument
  field_simp [hmR, hA0, hx0]

/-- The normalized Lambert argument is strictly decreasing on the
nonnegative input half-line. -/
theorem powerExponentialLambertArgument_strictAntiOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    StrictAntiOn (powerExponentialLambertArgument m A beta) (Ici 0) := by
  intro x hx y _hy hxy
  have hratio : x / A < y / A :=
    (div_lt_div_iff_of_pos_right hA).2 hxy
  have hpow := Real.rpow_lt_rpow (div_nonneg (mem_Ici.mp hx) hA.le)
    hratio (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)))
  have hscale : 0 < beta / (m : ℝ) :=
    div_pos hbeta (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  have hmul := mul_lt_mul_of_pos_left hpow hscale
  unfold powerExponentialLambertArgument
  linarith

/-- The normalized Lambert argument is continuous for every natural power
and every real amplitude and rate. -/
theorem powerExponentialLambertArgument_continuous
    (m : ℕ) (A beta : ℝ) :
    Continuous (powerExponentialLambertArgument m A beta) := by
  unfold powerExponentialLambertArgument
  exact (continuous_const.mul
    ((Real.continuous_rpow_const
      (inv_nonneg.mpr (Nat.cast_nonneg m))).comp
        (continuous_id.div_const A))).neg

/-- **Branch-generic inverse-profile derivative.**  Let `W` be any real
Lambert branch, i.e. a function satisfying the inverse-derivative law
`W' = (eᵂ (W + 1))⁻¹` and the defining equation `W u · e^(W u) = u` at
the normalized argument `u` (`powerExponentialLambertArgument m A beta`
at `x`), with `W u ≠ -1`.  Then the phase
`y ↦ -(m / beta) · W (argument y)` has derivative
`lambda / (x (m - beta lambda))` at `x`, where `lambda` is its value at
`x`.  Both concrete phases are instances. -/
theorem powerExponentialPhase_hasDerivAt_of_branch
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) (hx : 0 < x) {W : ℝ → ℝ}
    (hW : HasDerivAt W
      (Real.exp (W (powerExponentialLambertArgument m A beta x)) *
        (W (powerExponentialLambertArgument m A beta x) + 1))⁻¹
      (powerExponentialLambertArgument m A beta x))
    (hW1 : W (powerExponentialLambertArgument m A beta x) + 1 ≠ 0)
    (hwu : W (powerExponentialLambertArgument m A beta x) *
        Real.exp (W (powerExponentialLambertArgument m A beta x)) =
      powerExponentialLambertArgument m A beta x) :
    HasDerivAt
      (fun y : ℝ ↦ -((m : ℝ) / beta) *
        W (powerExponentialLambertArgument m A beta y))
      (-((m : ℝ) / beta) *
          W (powerExponentialLambertArgument m A beta x) /
        (x * ((m : ℝ) - beta * (-((m : ℝ) / beta) *
          W (powerExponentialLambertArgument m A beta x))))) x := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hbeta0 : beta ≠ 0 := hbeta.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hcomp := hW.comp x
    (powerExponentialLambertArgument_hasDerivAt hm hA hx)
  have hscaled := hcomp.const_mul (-((m : ℝ) / beta))
  let u := powerExponentialLambertArgument m A beta x
  let w := W u
  have hwu' : w * Real.exp w = u := by
    dsimp only [w, u]
    exact hwu
  have hW1' : w + 1 ≠ 0 := by
    dsimp only [w, u]
    exact hW1
  refine hscaled.congr_deriv ?_
  change
    (-((m : ℝ) / beta)) *
        ((Real.exp w * (w + 1))⁻¹ * (u / ((m : ℝ) * x))) =
      ((-((m : ℝ) / beta)) * w) /
        (x * ((m : ℝ) - beta * ((-((m : ℝ) / beta)) * w)))
  have hW1'' : (1 : ℝ) + w ≠ 0 := by
    rwa [add_comm] at hW1'
  rw [← hwu']
  field_simp [hmR, hbeta0, hx0, hW1', hW1'', Real.exp_ne_zero]
  ring

/-- Interior derivative of the principal power--exponential phase, in
inverse-profile coordinates. -/
theorem principalPowerExponentialPhase_hasDerivAt
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    HasDerivAt (principalPowerExponentialPhase m A beta)
      (principalPowerExponentialPhase m A beta x /
        (x * ((m : ℝ) - beta *
          principalPowerExponentialPhase m A beta x))) x := by
  have harg := powerExponentialLambertArgument_mem_Ioo hm hA hbeta hx
  have hW1 : principalLambertW
      (powerExponentialLambertArgument m A beta x) + 1 ≠ 0 := by
    linarith [neg_one_lt_principalLambertW harg.1]
  unfold principalPowerExponentialPhase
  exact powerExponentialPhase_hasDerivAt_of_branch hm hA hbeta hx.1
    (principalLambertW_hasDerivAt harg.1) hW1
    (principalLambertW_mul_exp harg.1.le)

/-- Interior derivative of the lower power--exponential phase, in
inverse-profile coordinates. -/
theorem lowerPowerExponentialPhase_hasDerivAt
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    HasDerivAt (lowerPowerExponentialPhase m A beta)
      (lowerPowerExponentialPhase m A beta x /
        (x * ((m : ℝ) - beta *
          lowerPowerExponentialPhase m A beta x))) x := by
  have harg := powerExponentialLambertArgument_mem_Ioo hm hA hbeta hx
  have hW1 : lowerLambertW
      (powerExponentialLambertArgument m A beta x) + 1 ≠ 0 := by
    linarith [lowerLambertW_lt_neg_one harg]
  unfold lowerPowerExponentialPhase
  exact powerExponentialPhase_hasDerivAt_of_branch hm hA hbeta hx.1
    (lowerLambertW_hasDerivAt harg) hW1
    (lowerLambertW_mul_exp harg)

/-- Quotient formula for the derivative of the principal phase. -/
theorem deriv_principalPowerExponentialPhase
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    deriv (principalPowerExponentialPhase m A beta) x =
      principalPowerExponentialPhase m A beta x /
        (x * ((m : ℝ) - beta *
          principalPowerExponentialPhase m A beta x)) :=
  (principalPowerExponentialPhase_hasDerivAt hm hA hbeta hx).deriv

/-- Quotient formula for the derivative of the lower phase. -/
theorem deriv_lowerPowerExponentialPhase
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    deriv (lowerPowerExponentialPhase m A beta) x =
      lowerPowerExponentialPhase m A beta x /
        (x * ((m : ℝ) - beta *
          lowerPowerExponentialPhase m A beta x)) :=
  (lowerPowerExponentialPhase_hasDerivAt hm hA hbeta hx).deriv

/-- The principal phase is continuous throughout its smooth interior. -/
theorem principalPowerExponentialPhase_continuousOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    ContinuousOn (principalPowerExponentialPhase m A beta)
      (Ioo 0 (powerExponentialPeak m A beta)) :=
  fun _ hx =>
    (principalPowerExponentialPhase_hasDerivAt hm hA hbeta hx).continuousAt.continuousWithinAt

/-- The lower phase is continuous throughout its smooth interior. -/
theorem lowerPowerExponentialPhase_continuousOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    ContinuousOn (lowerPowerExponentialPhase m A beta)
      (Ioo 0 (powerExponentialPeak m A beta)) :=
  fun _ hx =>
    (lowerPowerExponentialPhase_hasDerivAt hm hA hbeta hx).continuousAt.continuousWithinAt

/-- The principal phase is continuous on its full closed profile-value
interval, including zero and the common branch point at the peak. -/
theorem principalPowerExponentialPhase_continuousOn_Icc
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    ContinuousOn (principalPowerExponentialPhase m A beta)
      (Icc 0 (powerExponentialPeak m A beta)) := by
  unfold principalPowerExponentialPhase
  exact continuousOn_const.mul <|
    principalLambertW_continuousOn_Ici.comp
      (powerExponentialLambertArgument_continuous m A beta).continuousOn
      fun x hx ↦ mem_Ici.mpr
        (powerExponentialLambertArgument_mem_Icc hm hA hbeta hx).1

/-- The lower phase is continuous on its full positive endpoint-inclusive
profile-value interval.  The input zero is excluded because the lower inverse
diverges there. -/
theorem lowerPowerExponentialPhase_continuousOn_Ioc
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    ContinuousOn (lowerPowerExponentialPhase m A beta)
      (Ioc 0 (powerExponentialPeak m A beta)) := by
  unfold lowerPowerExponentialPhase
  exact continuousOn_const.mul <|
    lowerLambertW_continuousOn_Ico.comp
      (powerExponentialLambertArgument_continuous m A beta).continuousOn
      fun x hx ↦ powerExponentialLambertArgument_mem_Ico hm hA hbeta hx

/-- The principal phase has positive derivative on the smooth interior. -/
theorem deriv_principalPowerExponentialPhase_pos
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    0 < deriv (principalPowerExponentialPhase m A beta) x := by
  rw [deriv_principalPowerExponentialPhase hm hA hbeta hx]
  have hden : 0 < (m : ℝ) - beta *
      principalPowerExponentialPhase m A beta x := by
    have h := (lt_div_iff₀ hbeta).mp
      (principalPowerExponentialPhase_lt_turningPoint hm hA hbeta hx)
    nlinarith
  exact div_pos (principalPowerExponentialPhase_pos hm hA hbeta hx)
    (mul_pos hx.1 hden)

/-- The lower phase has negative derivative on the smooth interior. -/
theorem deriv_lowerPowerExponentialPhase_neg
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    deriv (lowerPowerExponentialPhase m A beta) x < 0 := by
  rw [deriv_lowerPowerExponentialPhase hm hA hbeta hx]
  have hturn : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  have hphase := turningPoint_lt_lowerPowerExponentialPhase hm hA hbeta hx
  have hden : (m : ℝ) - beta *
      lowerPowerExponentialPhase m A beta x < 0 := by
    have h := (div_lt_iff₀ hbeta).mp hphase
    nlinarith
  exact div_neg_of_pos_of_neg (lt_trans hturn hphase)
    (mul_neg_of_pos_of_neg hx.1 hden)

/-- The principal phase is strictly increasing on the full closed interval
from zero to the profile peak. -/
theorem principalPowerExponentialPhase_strictMonoOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    StrictMonoOn (principalPowerExponentialPhase m A beta)
      (Icc 0 (powerExponentialPeak m A beta)) := by
  intro x hx y hy hxy
  have hargx := powerExponentialLambertArgument_mem_Icc hm hA hbeta hx
  have hargy := powerExponentialLambertArgument_mem_Icc hm hA hbeta hy
  have harglt := powerExponentialLambertArgument_strictAntiOn hm hA hbeta
    (mem_Ici.mpr hx.1) (mem_Ici.mpr hy.1) hxy
  have hW := principalLambertW_strictMonoOn
    (mem_Ici.mpr hargy.1) (mem_Ici.mpr hargx.1) harglt
  have hscale : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  unfold principalPowerExponentialPhase
  nlinarith

/-- The lower phase is strictly decreasing on the positive interval through
the common peak endpoint. -/
theorem lowerPowerExponentialPhase_strictAntiOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    StrictAntiOn (lowerPowerExponentialPhase m A beta)
      (Ioc 0 (powerExponentialPeak m A beta)) := by
  intro x hx y hy hxy
  have hargx := powerExponentialLambertArgument_mem_Ico hm hA hbeta hx
  have hargy := powerExponentialLambertArgument_mem_Ico hm hA hbeta hy
  have harglt := powerExponentialLambertArgument_strictAntiOn hm hA hbeta
    (mem_Ici.mpr hx.1.le) (mem_Ici.mpr hy.1.le) hxy
  have hW := lowerLambertW_strictAntiOn_Ico hargy hargx harglt
  have hscale : 0 < (m : ℝ) / beta :=
    div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
  unfold lowerPowerExponentialPhase
  nlinarith

end

end Fabius
