import FabiusFunction.PowerExponentialLambertCalculus

/-!
# Exact inverse geometry of scaled power--exponential profiles

This module upgrades the solve laws for the two Lambert phases to exact
range and inverse statements.  For nonzero natural power `m`, positive
amplitude `A`, and positive rate `beta`, the normalized Lambert argument
maps the closed input interval exactly onto `[-exp (-1), 0]` and maps its
positive half-open part exactly onto `[-exp (-1), 0)`.  Combining those
identities with the exact ranges of the two real Lambert branches gives

* the principal phase image `[0, m / beta]`;
* the lower phase image `[m / beta, ∞)`;
* full `InvOn` laws between each phase and `powerExponentialSaddle` on the
  corresponding branch domains.

The range proofs are algebraic: they invert the normalized Lambert argument
explicitly and then use the exact branch images.  No endpoint continuity or
global calculus theorem is needed.
-/

set_option autoImplicit false

open Set Function

namespace Fabius

noncomputable section

/-- The normalized Lambert argument maps the closed profile-value interval
exactly onto `[-exp (-1), 0]`. -/
theorem powerExponentialLambertArgument_image_Icc
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    powerExponentialLambertArgument m A beta ''
        Icc 0 (powerExponentialPeak m A beta) =
      Icc (-Real.exp (-1)) 0 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact powerExponentialLambertArgument_mem_Icc hm hA hbeta hx
  · intro z hz
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hturn : 0 < (m : ℝ) / beta :=
      div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
    let q : ℝ := -((m : ℝ) / beta) * z
    let x : ℝ := A * q ^ m
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr hturn.le) hz.2
    have hqle : q ≤ ((m : ℝ) / beta) * Real.exp (-1) := by
      dsimp only [q]
      calc
        -((m : ℝ) / beta) * z ≤
            -((m : ℝ) / beta) * (-Real.exp (-1)) :=
          mul_le_mul_of_nonpos_left hz.1 (neg_nonpos.mpr hturn.le)
        _ = ((m : ℝ) / beta) * Real.exp (-1) := by ring
    have hx : x ∈ Icc 0 (powerExponentialPeak m A beta) := by
      constructor
      · dsimp only [x]
        exact mul_nonneg hA.le (pow_nonneg hq0 m)
      · rw [powerExponentialPeak]
        dsimp only [x]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hq0 hqle m) hA.le
    refine ⟨x, hx, ?_⟩
    have hxdiv : x / A = q ^ m := by
      dsimp only [x]
      field_simp [hA.ne']
    have hroot : (x / A) ^ ((m : ℝ)⁻¹) = q := by
      rw [hxdiv]
      exact Real.pow_rpow_inv_natCast hq0 hm
    rw [powerExponentialLambertArgument, hroot]
    dsimp only [q]
    field_simp [hmR, hbeta.ne']

/-- The normalized Lambert argument maps the positive endpoint-inclusive
profile-value interval exactly onto `[-exp (-1), 0)`. -/
theorem powerExponentialLambertArgument_image_Ioc
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    powerExponentialLambertArgument m A beta ''
        Ioc 0 (powerExponentialPeak m A beta) =
      Ico (-Real.exp (-1)) 0 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact powerExponentialLambertArgument_mem_Ico hm hA hbeta hx
  · intro z hz
    have hzclosed : z ∈ Icc (-Real.exp (-1)) 0 := ⟨hz.1, hz.2.le⟩
    rw [← powerExponentialLambertArgument_image_Icc hm hA hbeta] at hzclosed
    obtain ⟨x, hx, hxz⟩ := hzclosed
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hxne : x ≠ 0 := by
      intro hzero
      subst x
      have hzeroarg : (0 : ℝ) = z := by
        simpa only [powerExponentialLambertArgument, zero_div,
          Real.zero_rpow (inv_ne_zero hmR), mul_zero, neg_zero] using hxz
      exact hz.2.ne hzeroarg.symm
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hxne), hx.2⟩, hxz⟩

/-- Exact range of the principal scaled power--exponential phase on the
closed input interval. -/
theorem principalPowerExponentialPhase_image_Icc
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    principalPowerExponentialPhase m A beta ''
        Icc 0 (powerExponentialPeak m A beta) =
      Icc 0 ((m : ℝ) / beta) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact principalPowerExponentialPhase_mem_Icc hm hA hbeta hx
  · intro y hy
    have hturn : 0 < (m : ℝ) / beta :=
      div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
    let w : ℝ := -(y / ((m : ℝ) / beta))
    have hw : w ∈ Icc (-1) 0 := by
      constructor
      · dsimp only [w]
        have hquot : y / ((m : ℝ) / beta) ≤ 1 :=
          (div_le_one hturn).2 hy.2
        linarith
      · dsimp only [w]
        exact neg_nonpos.mpr (div_nonneg hy.1 hturn.le)
    rw [← principalLambertW_image_Icc] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    rw [← powerExponentialLambertArgument_image_Icc hm hA hbeta] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨x, hx, ?_⟩
    unfold principalPowerExponentialPhase
    rw [hxz, hzw]
    dsimp only [w]
    calc
      -((m : ℝ) / beta) *
          -(y / ((m : ℝ) / beta)) =
          y / ((m : ℝ) / beta) * ((m : ℝ) / beta) := by ring
      _ = y := div_mul_cancel₀ y hturn.ne'

/-- Exact range of the lower scaled power--exponential phase on the positive
endpoint-inclusive input interval. -/
theorem lowerPowerExponentialPhase_image_Ioc
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    lowerPowerExponentialPhase m A beta ''
        Ioc 0 (powerExponentialPeak m A beta) =
      Ici ((m : ℝ) / beta) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact lowerPowerExponentialPhase_mem_Ici hm hA hbeta hx
  · intro y hy
    have hturn : 0 < (m : ℝ) / beta :=
      div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hbeta
    let w : ℝ := -(y / ((m : ℝ) / beta))
    have hw : w ∈ Iic (-1) := by
      dsimp only [w]
      have hquot : 1 ≤ y / ((m : ℝ) / beta) :=
        (le_div_iff₀ hturn).2
          (by simpa only [one_mul] using (mem_Ici.mp hy))
      exact neg_le_neg hquot
    rw [← lowerLambertW_image_Ico] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    rw [← powerExponentialLambertArgument_image_Ioc hm hA hbeta] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨x, hx, ?_⟩
    unfold lowerPowerExponentialPhase
    rw [hxz, hzw]
    dsimp only [w]
    calc
      -((m : ℝ) / beta) *
          -(y / ((m : ℝ) / beta)) =
          y / ((m : ℝ) / beta) * ((m : ℝ) / beta) := by ring
      _ = y := div_mul_cancel₀ y hturn.ne'

/-- On the principal lambda interval, the principal phase recovers the
lambda coordinate after evaluating the scaled power--exponential profile. -/
theorem principalPowerExponentialPhase_leftInvOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    LeftInvOn (principalPowerExponentialPhase m A beta)
      (powerExponentialSaddle m A beta)
      (Icc 0 ((m : ℝ) / beta)) := by
  intro lambda hlambda
  have himage : lambda ∈ principalPowerExponentialPhase m A beta ''
      Icc 0 (powerExponentialPeak m A beta) := by
    rw [principalPowerExponentialPhase_image_Icc hm hA hbeta]
    exact hlambda
  obtain ⟨x, hx, hphase⟩ := himage
  calc
    principalPowerExponentialPhase m A beta
        (powerExponentialSaddle m A beta lambda) =
        principalPowerExponentialPhase m A beta x := by
      rw [← hphase, principalPowerExponentialPhase_solves hm hA hbeta hx]
    _ = lambda := hphase

/-- On the closed profile-value interval, the scaled power--exponential
profile recovers the input after applying the principal phase. -/
theorem principalPowerExponentialPhase_rightInvOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    RightInvOn (principalPowerExponentialPhase m A beta)
      (powerExponentialSaddle m A beta)
      (Icc 0 (powerExponentialPeak m A beta)) :=
  fun _ hx ↦ principalPowerExponentialPhase_solves hm hA hbeta hx

/-- The principal phase and the scaled power--exponential profile are exact
setwise inverses between `[0, m / beta]` and the closed profile-value
interval. -/
theorem principalPowerExponentialPhase_invOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    InvOn (principalPowerExponentialPhase m A beta)
      (powerExponentialSaddle m A beta)
      (Icc 0 ((m : ℝ) / beta))
      (Icc 0 (powerExponentialPeak m A beta)) :=
  ⟨principalPowerExponentialPhase_leftInvOn hm hA hbeta,
    principalPowerExponentialPhase_rightInvOn hm hA hbeta⟩

/-- On the upper lambda half-line, the lower phase recovers the lambda
coordinate after evaluating the scaled power--exponential profile. -/
theorem lowerPowerExponentialPhase_leftInvOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    LeftInvOn (lowerPowerExponentialPhase m A beta)
      (powerExponentialSaddle m A beta)
      (Ici ((m : ℝ) / beta)) := by
  intro lambda hlambda
  have himage : lambda ∈ lowerPowerExponentialPhase m A beta ''
      Ioc 0 (powerExponentialPeak m A beta) := by
    rw [lowerPowerExponentialPhase_image_Ioc hm hA hbeta]
    exact hlambda
  obtain ⟨x, hx, hphase⟩ := himage
  calc
    lowerPowerExponentialPhase m A beta
        (powerExponentialSaddle m A beta lambda) =
        lowerPowerExponentialPhase m A beta x := by
      rw [← hphase, lowerPowerExponentialPhase_solves hm hA hbeta hx]
    _ = lambda := hphase

/-- On the positive endpoint-inclusive profile-value interval, the scaled
power--exponential profile recovers the input after applying the lower
phase. -/
theorem lowerPowerExponentialPhase_rightInvOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    RightInvOn (lowerPowerExponentialPhase m A beta)
      (powerExponentialSaddle m A beta)
      (Ioc 0 (powerExponentialPeak m A beta)) :=
  fun _ hx ↦ lowerPowerExponentialPhase_solves hm hA hbeta hx

/-- The lower phase and the scaled power--exponential profile are exact
setwise inverses between `[m / beta, ∞)` and the positive endpoint-inclusive
profile-value interval. -/
theorem lowerPowerExponentialPhase_invOn
    {m : ℕ} (hm : m ≠ 0) {A beta : ℝ}
    (hA : 0 < A) (hbeta : 0 < beta) :
    InvOn (lowerPowerExponentialPhase m A beta)
      (powerExponentialSaddle m A beta)
      (Ici ((m : ℝ) / beta))
      (Ioc 0 (powerExponentialPeak m A beta)) :=
  ⟨lowerPowerExponentialPhase_leftInvOn hm hA hbeta,
    lowerPowerExponentialPhase_rightInvOn hm hA hbeta⟩

end

end Fabius
