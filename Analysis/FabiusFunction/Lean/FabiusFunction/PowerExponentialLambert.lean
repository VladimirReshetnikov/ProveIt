import FabiusFunction.LowerLambertW
import FabiusFunction.PrincipalLambertW

/-!
# Lambert inverses of scaled power--exponential profiles

This module packages the two nonnegative inverse branches of

`lambda ↦ A * lambda ^ m * exp (-beta * lambda)`

for a positive amplitude `A`, positive rate `beta`, and nonzero natural
power `m`.  The turning point is `m / beta`; the corresponding peak value is
chosen in a form that makes the natural Lambert-domain calculation literal.

The principal branch starts at zero and rises to the turning point.  The
lower branch runs from the turning point to infinity.  Both are totalized as
functions, but their exact solve laws below carry the natural compact or
half-open input domains explicitly.  No asymptotic, differentiability, or
probabilistic assumption is used.

## Main declarations

* `powerExponentialSaddle` is the scaled power--exponential profile.
* `powerExponentialPeak` is its value at `m / beta`.
* `powerExponentialLambertArgument` is the normalized real Lambert argument.
* `principalPowerExponentialPhase` and `lowerPowerExponentialPhase` are the
  two real inverse branches.
* `principalPowerExponentialPhase_solves` and
  `lowerPowerExponentialPhase_solves` prove the exact inverse equations on
  their natural domains, including the common finite branch point.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-- The scaled power--exponential profile
`A * lambda ^ m * exp (-beta * lambda)`. -/
noncomputable def powerExponentialSaddle
    (m : ℕ) (A beta lambda : ℝ) : ℝ :=
  A * lambda ^ m * Real.exp (-beta * lambda)

/-- The peak value of `powerExponentialSaddle`, attained at `m / beta` when
`m ≠ 0`, `A > 0`, and `beta > 0`.

The definition is `A * ((m / beta) * exp (-1)) ^ m`; a separate theorem
rewrites it as `A * (m / beta) ^ m * exp (-m)`. -/
noncomputable def powerExponentialPeak (m : ℕ) (A beta : ℝ) : ℝ :=
  A * (((m : ℝ) / beta) * Real.exp (-1)) ^ m

/-- The normalized Lambert argument associated with the equation
`A * lambda ^ m * exp (-beta * lambda) = x`. -/
noncomputable def powerExponentialLambertArgument
    (m : ℕ) (A beta x : ℝ) : ℝ :=
  -(beta / (m : ℝ) * (x / A) ^ ((m : ℝ)⁻¹))

/-- The principal real inverse branch of the scaled power--exponential
profile. -/
noncomputable def principalPowerExponentialPhase
    (m : ℕ) (A beta x : ℝ) : ℝ :=
  -((m : ℝ) / beta) *
    principalLambertW (powerExponentialLambertArgument m A beta x)

/-- The lower real inverse branch of the scaled power--exponential profile. -/
noncomputable def lowerPowerExponentialPhase
    (m : ℕ) (A beta x : ℝ) : ℝ :=
  -((m : ℝ) / beta) *
    lowerLambertW (powerExponentialLambertArgument m A beta x)

/-- The conventional closed form of the peak value. -/
theorem powerExponentialPeak_eq
    (m : ℕ) (A beta : ℝ) :
    powerExponentialPeak m A beta =
      A * ((m : ℝ) / beta) ^ m * Real.exp (-(m : ℝ)) := by
  rw [powerExponentialPeak, mul_pow, ← Real.exp_nat_mul]
  have hexp : Real.exp ((m : ℝ) * -1) = Real.exp (-(m : ℝ)) := by
    congr 1
    ring
  rw [hexp]
  ring

private lemma powerExponentialBase_pos
    {m : ℕ} (hm : m ≠ 0) {beta : ℝ} (hbeta : 0 < beta) :
    0 < ((m : ℝ) / beta) * Real.exp (-1) := by
  exact mul_pos (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta)
    (Real.exp_pos _)

/-- The profile peak is strictly positive under the natural positive
parameters. -/
theorem powerExponentialPeak_pos
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    0 < powerExponentialPeak m A beta := by
  rw [powerExponentialPeak]
  exact mul_pos hA (pow_pos (powerExponentialBase_pos hm hbeta) m)

/-- Evaluating the profile at its turning point gives its declared peak. -/
@[simp] theorem powerExponentialSaddle_turningPoint
    (m : ℕ) (A : ℝ) {beta : ℝ} (hbeta : beta ≠ 0) :
    powerExponentialSaddle m A beta ((m : ℝ) / beta) =
      powerExponentialPeak m A beta := by
  rw [powerExponentialSaddle, powerExponentialPeak_eq]
  have hexp : -beta * ((m : ℝ) / beta) = -(m : ℝ) := by
    field_simp [hbeta]
  rw [hexp]

private lemma powerExponentialRatio_mem_Icc
    {m : ℕ} {A beta x : ℝ} (hA : 0 < A)
    (hx : x ∈ Icc 0 (powerExponentialPeak m A beta)) :
    x / A ∈ Icc 0
      ((((m : ℝ) / beta) * Real.exp (-1)) ^ m) := by
  constructor
  · exact div_nonneg hx.1 hA.le
  · rw [powerExponentialPeak] at hx
    exact (div_le_iff₀ hA).2 (by simpa [mul_comm] using hx.2)

private lemma powerExponentialRoot_le
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Icc 0 (powerExponentialPeak m A beta)) :
    (x / A) ^ ((m : ℝ)⁻¹) ≤
      ((m : ℝ) / beta) * Real.exp (-1) := by
  have hratio := powerExponentialRatio_mem_Icc hA hx
  have hroot := Real.rpow_le_rpow hratio.1 hratio.2
    (inv_nonneg.mpr (Nat.cast_nonneg m))
  have hbase := powerExponentialBase_pos hm hbeta
  simpa only [Real.pow_rpow_inv_natCast hbase.le hm] using hroot

/-- The normalized Lambert argument maps the closed input interval from zero
to the profile peak into the common closed real Lambert domain. -/
theorem powerExponentialLambertArgument_mem_Icc
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Icc 0 (powerExponentialPeak m A beta)) :
    powerExponentialLambertArgument m A beta x ∈
      Icc (-Real.exp (-1)) 0 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hroot0 : 0 ≤ (x / A) ^ ((m : ℝ)⁻¹) :=
    Real.rpow_nonneg (div_nonneg hx.1 hA.le) _
  have hroot := powerExponentialRoot_le hm hA hbeta hx
  have hscale : 0 < beta / (m : ℝ) :=
    div_pos hbeta (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  constructor
  · unfold powerExponentialLambertArgument
    have hmul := mul_le_mul_of_nonneg_left hroot hscale.le
    have hsimp : beta / (m : ℝ) *
        (((m : ℝ) / beta) * Real.exp (-1)) = Real.exp (-1) := by
      field_simp [hmR, hbeta.ne']
    rw [hsimp] at hmul
    linarith
  · unfold powerExponentialLambertArgument
    exact neg_nonpos.mpr (mul_nonneg hscale.le hroot0)

/-- Positive inputs up to the peak give the closed-left lower-Lambert
domain; zero is excluded because the lower branch has no finite value there. -/
theorem powerExponentialLambertArgument_mem_Ico
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioc 0 (powerExponentialPeak m A beta)) :
    powerExponentialLambertArgument m A beta x ∈
      Ico (-Real.exp (-1)) 0 := by
  have hclosed := powerExponentialLambertArgument_mem_Icc hm hA hbeta
    ⟨hx.1.le, hx.2⟩
  refine ⟨hclosed.1, ?_⟩
  unfold powerExponentialLambertArgument
  have hratio : 0 < x / A := div_pos hx.1 hA
  have hroot : 0 < (x / A) ^ ((m : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hratio _
  have hscale : 0 < beta / (m : ℝ) :=
    div_pos hbeta (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  exact neg_lt_zero.mpr (mul_pos hscale hroot)

/-- Inputs strictly between zero and the peak give the smooth common
Lambert domain. -/
theorem powerExponentialLambertArgument_mem_Ioo
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m A beta)) :
    powerExponentialLambertArgument m A beta x ∈
      Ioo (-Real.exp (-1)) 0 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hbase := powerExponentialBase_pos hm hbeta
  have hratio : x / A ∈ Ico 0
      ((((m : ℝ) / beta) * Real.exp (-1)) ^ m) := by
    constructor
    · exact div_nonneg hx.1.le hA.le
    · rw [powerExponentialPeak] at hx
      exact (div_lt_iff₀ hA).2 (by simpa [mul_comm] using hx.2)
  have hroot := Real.rpow_lt_rpow hratio.1 hratio.2
    (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)))
  have hroot' : (x / A) ^ ((m : ℝ)⁻¹) <
      ((m : ℝ) / beta) * Real.exp (-1) := by
    simpa only [Real.pow_rpow_inv_natCast hbase.le hm] using hroot
  have hscale : 0 < beta / (m : ℝ) :=
    div_pos hbeta (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
  have hmul := mul_lt_mul_of_pos_left hroot' hscale
  have hsimp : beta / (m : ℝ) *
      (((m : ℝ) / beta) * Real.exp (-1)) = Real.exp (-1) := by
    field_simp [hmR, hbeta.ne']
  rw [hsimp] at hmul
  refine ⟨?_, (powerExponentialLambertArgument_mem_Ico hm hA hbeta
    ⟨hx.1, hx.2.le⟩).2⟩
  unfold powerExponentialLambertArgument
  linarith

/-- Algebraic solve law shared by both real Lambert branches.  Any `w`
satisfying the normalized Lambert equation produces a solution of the
original scaled power--exponential equation. -/
theorem powerExponentialSaddle_scaledLambert_solution
    {m : ℕ} (hm : m ≠ 0) {A beta x w : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) (hx : 0 ≤ x)
    (hw : w * Real.exp w =
      powerExponentialLambertArgument m A beta x) :
    powerExponentialSaddle m A beta
      (-((m : ℝ) / beta) * w) = x := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hratio : 0 ≤ x / A := div_nonneg hx hA.le
  have hroot : ((x / A) ^ ((m : ℝ)⁻¹)) ^ m = x / A :=
    Real.rpow_inv_natCast_pow hratio hm
  have hexp : Real.exp
      (-beta * (-((m : ℝ) / beta) * w)) =
      Real.exp w ^ m := by
    rw [show -beta * (-((m : ℝ) / beta) * w) = (m : ℝ) * w by
      field_simp [hbeta.ne']]
    exact Real.exp_nat_mul w m
  have hmul : (-((m : ℝ) / beta) * w) * Real.exp w =
      (x / A) ^ ((m : ℝ)⁻¹) := by
    rw [mul_assoc, hw]
    unfold powerExponentialLambertArgument
    field_simp [hmR, hbeta.ne']
  unfold powerExponentialSaddle
  rw [hexp, mul_assoc, ← mul_pow, hmul, hroot]
  field_simp [hA.ne']

/-- The principal phase solves the scaled power--exponential equation on the
closed interval from zero to the peak. -/
theorem principalPowerExponentialPhase_solves
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Icc 0 (powerExponentialPeak m A beta)) :
    powerExponentialSaddle m A beta
      (principalPowerExponentialPhase m A beta x) = x := by
  apply powerExponentialSaddle_scaledLambert_solution hm hA hbeta hx.1
  exact principalLambertW_mul_exp
    (powerExponentialLambertArgument_mem_Icc hm hA hbeta hx).1

/-- The lower phase solves the scaled power--exponential equation for every
positive input up to and including the peak. -/
theorem lowerPowerExponentialPhase_solves
    {m : ℕ} (hm : m ≠ 0) {A beta x : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta)
    (hx : x ∈ Ioc 0 (powerExponentialPeak m A beta)) :
    powerExponentialSaddle m A beta
      (lowerPowerExponentialPhase m A beta x) = x := by
  apply powerExponentialSaddle_scaledLambert_solution hm hA hbeta hx.1.le
  exact lowerLambertW_mul_exp_of_mem_Ico
    (powerExponentialLambertArgument_mem_Ico hm hA hbeta hx)

/-- The principal phase starts at zero. -/
@[simp] theorem principalPowerExponentialPhase_zero
    {m : ℕ} (hm : m ≠ 0) (A beta : ℝ) :
    principalPowerExponentialPhase m A beta 0 = 0 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [principalPowerExponentialPhase, powerExponentialLambertArgument,
    zero_div, Real.zero_rpow (inv_ne_zero hmR), mul_zero, neg_zero,
    principalLambertW_zero, mul_zero]

/-- At the profile peak, the normalized Lambert argument is exactly the
common branch point `-exp (-1)`. -/
@[simp] theorem powerExponentialLambertArgument_peak
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    powerExponentialLambertArgument m A beta
      (powerExponentialPeak m A beta) = -Real.exp (-1) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hbase := powerExponentialBase_pos hm hbeta
  have hratio : powerExponentialPeak m A beta / A =
      (((m : ℝ) / beta) * Real.exp (-1)) ^ m := by
    rw [powerExponentialPeak]
    field_simp [hA.ne']
  rw [powerExponentialLambertArgument, hratio,
    Real.pow_rpow_inv_natCast hbase.le hm]
  field_simp [hmR, hbeta.ne']

/-- Both real inverse branches meet at the turning point `m / beta`. -/
@[simp] theorem principalPowerExponentialPhase_peak
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    principalPowerExponentialPhase m A beta
      (powerExponentialPeak m A beta) = (m : ℝ) / beta := by
  rw [principalPowerExponentialPhase,
    powerExponentialLambertArgument_peak hm hA hbeta,
    principalLambertW_branchPoint]
  ring

/-- The lower inverse branch has the same turning-point value as the
principal branch. -/
@[simp] theorem lowerPowerExponentialPhase_peak
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    lowerPowerExponentialPhase m A beta
      (powerExponentialPeak m A beta) = (m : ℝ) / beta := by
  rw [lowerPowerExponentialPhase,
    powerExponentialLambertArgument_peak hm hA hbeta,
    lowerLambertW_branchPoint]
  ring

end

end Fabius
