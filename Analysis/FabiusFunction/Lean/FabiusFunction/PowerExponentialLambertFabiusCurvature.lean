import FabiusFunction.LambertWCurvature
import FabiusFunction.PowerExponentialLambertCurvature
import FabiusFunction.PowerExponentialLambertFabius

/-!
# Curvature of the two Fabius Lambert phases

The classical saddle profile `lambda * 2 ^ (-lambda)` has two nonnegative
inverse branches below its peak.  This module specializes the generic
power--exponential second derivative and the raw Lambert curvature API to
their exact geometry.

The principal phase is strictly convex on the whole half-line ending at the
peak, including negative inputs and zero.  The lower phase changes curvature
once, at input `2 * exp (-2) / log 2`, where its value is `2 / log 2`; it is
strictly convex before that point and strictly concave afterward.

The sign analysis of the lower phase is done once: on the smooth
interval its second derivative is a positive multiple of
`log 2 * phase - 2` (`deriv_deriv_fabiusLambertPhase_eq_pos_mul`), and
the two sign characterizations read off that factor.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Fabius

noncomputable section

/-- The profile value at which the lower Fabius Lambert phase changes
curvature. -/
noncomputable def fabiusLambertInflectionInput : ℝ :=
  2 * Real.exp (-2) / Real.log 2

/-- The lower-phase inflection input lies strictly between zero and the
classical profile peak. -/
theorem fabiusLambertInflectionInput_mem_Ioo :
    fabiusLambertInflectionInput ∈
      Ioo 0 (Real.exp (-1) / Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ⟨div_pos (mul_pos two_pos (Real.exp_pos _)) hlog,
    (div_lt_div_iff_of_pos_right hlog).2
      two_mul_exp_neg_two_lt_exp_neg_one⟩

/-- At the lower-phase inflection input the Fabius Lambert phase equals
`2 / log 2`. -/
@[simp] theorem fabiusLambertPhase_inflectionInput :
    fabiusLambertPhase fabiusLambertInflectionInput = 2 / Real.log 2 := by
  have hlog0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold fabiusLambertInflectionInput fabiusLambertPhase paperLambertN
  have harg :
      -(Real.log 2 * (2 * Real.exp (-2) / Real.log 2)) =
        -2 * Real.exp (-2) := by
    field_simp [hlog0]
  rw [harg, lowerLambertW_neg_two_mul_exp]
  field_simp [hlog0]

/-! ## Lower phase -/

/-- Exact second derivative of the lower Fabius Lambert phase on the smooth
profile-value interval. -/
theorem deriv_deriv_fabiusLambertPhase
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    deriv (deriv fabiusLambertPhase) x =
      Real.log 2 * fabiusLambertPhase x ^ 2 *
          (2 - Real.log 2 * fabiusLambertPhase x) /
        (x ^ 2 * (1 - Real.log 2 * fabiusLambertPhase x) ^ 3) := by
  have hx' : x ∈ Ioo 0
      (powerExponentialPeak 1 1 (Real.log 2)) := by
    rwa [powerExponentialPeak_one_one_log_two]
  have h := deriv_deriv_lowerPowerExponentialPhase
    (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
    zero_lt_one (Real.log_pos (by norm_num)) hx'
  have hfun : lowerPowerExponentialPhase 1 1 (Real.log 2) =
      fabiusLambertPhase := by
    funext y
    exact lowerPowerExponentialPhase_one_one_log_two y
  rw [hfun] at h
  rw [h]
  norm_num
  ring

/-- **The one sign analysis of the lower phase.**  On the smooth
profile-value interval the second derivative is a positive multiple of
`log 2 * phase - 2`. -/
private theorem deriv_deriv_fabiusLambertPhase_eq_pos_mul
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    ∃ c : ℝ, 0 < c ∧
      deriv (deriv fabiusLambertPhase) x =
        c * (Real.log 2 * fabiusLambertPhase x - 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx.1
  have hphase : 1 / Real.log 2 < fabiusLambertPhase x := by
    have hx' : x ∈ Ioo 0
        (powerExponentialPeak 1 1 (Real.log 2)) := by
      rwa [powerExponentialPeak_one_one_log_two]
    simpa only [Nat.cast_one, one_div,
      lowerPowerExponentialPhase_one_one_log_two] using
        (turningPoint_lt_lowerPowerExponentialPhase
          (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
          zero_lt_one hlog hx')
  have hphase0 : 0 < fabiusLambertPhase x :=
    lt_trans (div_pos zero_lt_one hlog) hphase
  have hbase : 1 - Real.log 2 * fabiusLambertPhase x < 0 := by
    have := (div_lt_iff₀ hlog).mp hphase
    linarith
  have hden : x ^ 2 * (1 - Real.log 2 * fabiusLambertPhase x) ^ 3 < 0 :=
    mul_neg_of_pos_of_neg hx2 ((show Odd 3 by decide).pow_neg hbase)
  have hlead : 0 < Real.log 2 * fabiusLambertPhase x ^ 2 :=
    mul_pos hlog (sq_pos_of_pos hphase0)
  refine ⟨-(Real.log 2 * fabiusLambertPhase x ^ 2 /
      (x ^ 2 * (1 - Real.log 2 * fabiusLambertPhase x) ^ 3)),
    neg_pos.mpr (div_neg_of_pos_of_neg hlead hden), ?_⟩
  rw [deriv_deriv_fabiusLambertPhase hx]
  ring

private theorem deriv_deriv_fabiusLambertPhase_pos_iff_phase
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    0 < deriv (deriv fabiusLambertPhase) x ↔
      2 / Real.log 2 < fabiusLambertPhase x := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hc, hmul⟩ := deriv_deriv_fabiusLambertPhase_eq_pos_mul hx
  rw [hmul, mul_pos_iff_of_pos_left hc, div_lt_iff₀ hlog]
  constructor <;> intro h <;> linarith

private theorem deriv_deriv_fabiusLambertPhase_neg_iff_phase
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    deriv (deriv fabiusLambertPhase) x < 0 ↔
      fabiusLambertPhase x < 2 / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hc, hmul⟩ := deriv_deriv_fabiusLambertPhase_eq_pos_mul hx
  rw [hmul, lt_div_iff₀ hlog]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with hcase | hcase
    · linarith [hcase.2]
    · exact absurd hcase.1 (not_lt.mpr hc.le)
  · intro h
    exact mul_neg_of_pos_of_neg hc (by linarith)

/-- The lower Fabius phase has positive second derivative exactly before its
inflection input. -/
theorem deriv_deriv_fabiusLambertPhase_pos_iff
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    0 < deriv (deriv fabiusLambertPhase) x ↔
      x < fabiusLambertInflectionInput := by
  rw [deriv_deriv_fabiusLambertPhase_pos_iff_phase hx]
  have hanti := lowerPowerExponentialPhase_strictAntiOn
    (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
    zero_lt_one (Real.log_pos (by norm_num))
  have hx' : x ∈ Ioc 0 (powerExponentialPeak 1 1 (Real.log 2)) := by
    rw [powerExponentialPeak_one_one_log_two]
    exact ⟨hx.1, hx.2.le⟩
  have hi' : fabiusLambertInflectionInput ∈
      Ioc 0 (powerExponentialPeak 1 1 (Real.log 2)) := by
    rw [powerExponentialPeak_one_one_log_two]
    exact ⟨fabiusLambertInflectionInput_mem_Ioo.1,
      fabiusLambertInflectionInput_mem_Ioo.2.le⟩
  have hcmp := hanti.lt_iff_gt hi' hx'
  simpa only [lowerPowerExponentialPhase_one_one_log_two,
    fabiusLambertPhase_inflectionInput] using hcmp

/-- The lower Fabius phase has negative second derivative exactly after its
inflection input. -/
theorem deriv_deriv_fabiusLambertPhase_neg_iff
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    deriv (deriv fabiusLambertPhase) x < 0 ↔
      fabiusLambertInflectionInput < x := by
  rw [deriv_deriv_fabiusLambertPhase_neg_iff_phase hx]
  have hanti := lowerPowerExponentialPhase_strictAntiOn
    (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
    zero_lt_one (Real.log_pos (by norm_num))
  have hx' : x ∈ Ioc 0 (powerExponentialPeak 1 1 (Real.log 2)) := by
    rw [powerExponentialPeak_one_one_log_two]
    exact ⟨hx.1, hx.2.le⟩
  have hi' : fabiusLambertInflectionInput ∈
      Ioc 0 (powerExponentialPeak 1 1 (Real.log 2)) := by
    rw [powerExponentialPeak_one_one_log_two]
    exact ⟨fabiusLambertInflectionInput_mem_Ioo.1,
      fabiusLambertInflectionInput_mem_Ioo.2.le⟩
  have hcmp := hanti.lt_iff_gt hx' hi'
  simpa only [lowerPowerExponentialPhase_one_one_log_two,
    fabiusLambertPhase_inflectionInput] using hcmp

/-- The lower Fabius phase has exactly one zero of its second derivative on
the smooth profile-value interval. -/
theorem deriv_deriv_fabiusLambertPhase_eq_zero_iff
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    deriv (deriv fabiusLambertPhase) x = 0 ↔
      x = fabiusLambertInflectionInput := by
  constructor
  · intro hzero
    rcases lt_trichotomy x fabiusLambertInflectionInput with hlt | heq | hgt
    · exact False.elim (((deriv_deriv_fabiusLambertPhase_pos_iff hx).2 hlt).ne'
        hzero)
    · exact heq
    · exact False.elim (((deriv_deriv_fabiusLambertPhase_neg_iff hx).2 hgt).ne
        hzero)
  · rintro rfl
    rw [deriv_deriv_fabiusLambertPhase
      fabiusLambertInflectionInput_mem_Ioo,
      fabiusLambertPhase_inflectionInput]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring

/-- The second derivative vanishes at the exact lower-phase inflection
input. -/
@[simp] theorem deriv_deriv_fabiusLambertPhase_inflectionInput :
    deriv (deriv fabiusLambertPhase) fabiusLambertInflectionInput = 0 :=
  (deriv_deriv_fabiusLambertPhase_eq_zero_iff
    fabiusLambertInflectionInput_mem_Ioo).2 rfl

/-- The lower Fabius Lambert phase is strictly convex from zero through its
inflection input. -/
theorem strictConvexOn_fabiusLambertPhase_left :
    StrictConvexOn ℝ (Ioc 0 fabiusLambertInflectionInput)
      fabiusLambertPhase := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioc _ _)
  · exact fabiusLambertPhase_continuousOn_Ioc.mono fun _ hx ↦
      ⟨hx.1, hx.2.trans fabiusLambertInflectionInput_mem_Ioo.2.le⟩
  · intro x hx
    rw [interior_Ioc] at hx
    show 0 < deriv (deriv fabiusLambertPhase) x
    exact (deriv_deriv_fabiusLambertPhase_pos_iff
      ⟨hx.1, hx.2.trans fabiusLambertInflectionInput_mem_Ioo.2⟩).2 hx.2

/-- The lower Fabius Lambert phase is strictly concave from its inflection
input through the finite profile peak. -/
theorem strictConcaveOn_fabiusLambertPhase_right :
    StrictConcaveOn ℝ
      (Icc fabiusLambertInflectionInput
        (Real.exp (-1) / Real.log 2)) fabiusLambertPhase := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
  · exact fabiusLambertPhase_continuousOn_Ioc.mono fun _ hx ↦
      ⟨fabiusLambertInflectionInput_mem_Ioo.1.trans_le hx.1, hx.2⟩
  · intro x hx
    rw [interior_Icc] at hx
    show deriv (deriv fabiusLambertPhase) x < 0
    exact (deriv_deriv_fabiusLambertPhase_neg_iff
      ⟨fabiusLambertInflectionInput_mem_Ioo.1.trans hx.1, hx.2⟩).2 hx.1

/-! ## Principal phase -/

/-- Global affine-coordinate formula for the principal Fabius Lambert
phase. -/
theorem fabiusPrincipalLambertPhase_eq_principalLambertW (x : ℝ) :
    fabiusPrincipalLambertPhase x =
      -principalLambertW (-(Real.log 2 * x)) / Real.log 2 := by
  have hlog0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold fabiusPrincipalLambertPhase principalPowerExponentialPhase
    powerExponentialLambertArgument
  norm_num
  field_simp [hlog0]

/-- The principal Fabius Lambert phase is continuous on the whole half-line
ending at its finite profile peak. -/
theorem fabiusPrincipalLambertPhase_continuousOn_Iic :
    ContinuousOn fabiusPrincipalLambertPhase
      (Iic (Real.exp (-1) / Real.log 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : ContinuousOn (fun x : ℝ ↦ -(Real.log 2 * x))
      (Iic (Real.exp (-1) / Real.log 2)) :=
    (continuous_const.mul continuous_id).neg.continuousOn
  have hcomp : ContinuousOn
      (fun x : ℝ ↦ principalLambertW (-(Real.log 2 * x)))
      (Iic (Real.exp (-1) / Real.log 2)) :=
    principalLambertW_continuousOn_Ici.comp harg fun x hx ↦ by
      have hmul := (le_div_iff₀ hlog).mp hx
      exact mem_Ici.mpr (by nlinarith)
  have hscaled : ContinuousOn
      (fun x : ℝ ↦ (-1 / Real.log 2) *
        principalLambertW (-(Real.log 2 * x)))
      (Iic (Real.exp (-1) / Real.log 2)) :=
    continuousOn_const.mul hcomp
  have hfun : fabiusPrincipalLambertPhase =
      (fun x : ℝ ↦ (-1 / Real.log 2) *
        principalLambertW (-(Real.log 2 * x))) := by
    funext x
    rw [fabiusPrincipalLambertPhase_eq_principalLambertW]
    ring
  rwa [hfun]

private theorem fabiusPrincipalLambertArgument_mem_Ioi
    {x : ℝ} (hx : x < Real.exp (-1) / Real.log 2) :
    -Real.exp (-1) < -(Real.log 2 * x) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := (lt_div_iff₀ hlog).mp hx
  nlinarith

/-- The principal Fabius phase is differentiable on the whole open half-line
below the peak, including negative inputs and zero. -/
theorem fabiusPrincipalLambertPhase_hasDerivAt
    {x : ℝ} (hx : x < Real.exp (-1) / Real.log 2) :
    HasDerivAt fabiusPrincipalLambertPhase
      (Real.exp (principalLambertW (-(Real.log 2 * x))) *
        (principalLambertW (-(Real.log 2 * x)) + 1))⁻¹ x := by
  have hlog0 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hu : HasDerivAt (fun y : ℝ ↦ -(Real.log 2 * y))
      (-Real.log 2) x :=
    (hasDerivAt_const_mul (x := x) (Real.log 2)).neg
  have hcomp := (principalLambertW_hasDerivAt
    (fabiusPrincipalLambertArgument_mem_Ioi hx)).comp x hu
  have hcomp' : HasDerivAt
      (fun y : ℝ ↦ principalLambertW (-(Real.log 2 * y)))
      ((Real.exp (principalLambertW (-(Real.log 2 * x))) *
        (principalLambertW (-(Real.log 2 * x)) + 1))⁻¹ *
        (-Real.log 2)) x := by
    have hfuncomp : (principalLambertW ∘
        (fun y : ℝ ↦ -(Real.log 2 * y))) =
        (fun y : ℝ ↦ principalLambertW (-(Real.log 2 * y))) := by
      funext y
      rfl
    rw [hfuncomp] at hcomp
    exact hcomp
  have hneg := hcomp'.neg
  have hfunneg : -(fun y : ℝ ↦
      principalLambertW (-(Real.log 2 * y))) =
      (fun y : ℝ ↦ -principalLambertW (-(Real.log 2 * y))) := by
    funext y
    rfl
  rw [hfunneg] at hneg
  have hraw := hneg.div_const (Real.log 2)
  have hfun : (fun y : ℝ ↦
      -principalLambertW (-(Real.log 2 * y)) / Real.log 2) =
      fabiusPrincipalLambertPhase := by
    funext y
    exact (fabiusPrincipalLambertPhase_eq_principalLambertW y).symm
  rw [hfun] at hraw
  apply hraw.congr_deriv
  field_simp [hlog0]

/-- Exact first derivative of the principal Fabius phase on the whole open
half-line below the peak. -/
theorem deriv_fabiusPrincipalLambertPhase
    {x : ℝ} (hx : x < Real.exp (-1) / Real.log 2) :
    deriv fabiusPrincipalLambertPhase x =
      (Real.exp (principalLambertW (-(Real.log 2 * x))) *
        (principalLambertW (-(Real.log 2 * x)) + 1))⁻¹ :=
  (fabiusPrincipalLambertPhase_hasDerivAt hx).deriv

/-- The derivative of the principal Fabius phase is differentiable on the
whole open half-line below the peak. -/
theorem deriv_fabiusPrincipalLambertPhase_hasDerivAt
    {x : ℝ} (hx : x < Real.exp (-1) / Real.log 2) :
    HasDerivAt (deriv fabiusPrincipalLambertPhase)
      (Real.log 2 *
        Real.exp (-2 * principalLambertW (-(Real.log 2 * x))) *
        (principalLambertW (-(Real.log 2 * x)) + 2) /
        (principalLambertW (-(Real.log 2 * x)) + 1) ^ 3) x := by
  have hu : HasDerivAt (fun y : ℝ ↦ -(Real.log 2 * y))
      (-Real.log 2) x :=
    (hasDerivAt_const_mul (x := x) (Real.log 2)).neg
  have hcomp := (deriv_principalLambertW_hasDerivAt
    (fabiusPrincipalLambertArgument_mem_Ioi hx)).comp x hu
  have hcomp' : HasDerivAt
      (fun y : ℝ ↦ deriv principalLambertW (-(Real.log 2 * y)))
      ((-Real.exp (-2 * principalLambertW (-(Real.log 2 * x))) *
          (principalLambertW (-(Real.log 2 * x)) + 2) /
          (principalLambertW (-(Real.log 2 * x)) + 1) ^ 3) *
        (-Real.log 2)) x := by
    have hfuncomp : (deriv principalLambertW ∘
        (fun y : ℝ ↦ -(Real.log 2 * y))) =
        (fun y : ℝ ↦ deriv principalLambertW (-(Real.log 2 * y))) := by
      funext y
      rfl
    rw [hfuncomp] at hcomp
    exact hcomp
  have heq : deriv fabiusPrincipalLambertPhase =ᶠ[nhds x]
      (fun y : ℝ ↦ deriv principalLambertW (-(Real.log 2 * y))) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [deriv_fabiusPrincipalLambertPhase hy,
      deriv_principalLambertW (fabiusPrincipalLambertArgument_mem_Ioi hy)]
  have hsecond := hcomp'.congr_of_eventuallyEq heq
  apply hsecond.congr_deriv
  ring

/-- Exact second derivative of the principal Fabius phase below the profile
peak. -/
theorem deriv_deriv_fabiusPrincipalLambertPhase
    {x : ℝ} (hx : x < Real.exp (-1) / Real.log 2) :
    deriv (deriv fabiusPrincipalLambertPhase) x =
      Real.log 2 *
        Real.exp (-2 * principalLambertW (-(Real.log 2 * x))) *
        (principalLambertW (-(Real.log 2 * x)) + 2) /
        (principalLambertW (-(Real.log 2 * x)) + 1) ^ 3 :=
  (deriv_fabiusPrincipalLambertPhase_hasDerivAt hx).deriv

/-- The principal Fabius phase has positive second derivative everywhere
below its peak. -/
theorem deriv_deriv_fabiusPrincipalLambertPhase_pos
    {x : ℝ} (hx : x < Real.exp (-1) / Real.log 2) :
    0 < deriv (deriv fabiusPrincipalLambertPhase) x := by
  rw [deriv_deriv_fabiusPrincipalLambertPhase hx]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hW := neg_one_lt_principalLambertW
    (fabiusPrincipalLambertArgument_mem_Ioi hx)
  exact div_pos
    (mul_pos (mul_pos hlog (Real.exp_pos _)) (by linarith))
    (pow_pos (by linarith) 3)

/-- At zero, the principal Fabius phase has second derivative
`2 * log 2`. -/
@[simp] theorem deriv_deriv_fabiusPrincipalLambertPhase_zero :
    deriv (deriv fabiusPrincipalLambertPhase) 0 = 2 * Real.log 2 := by
  rw [deriv_deriv_fabiusPrincipalLambertPhase
    (div_pos (Real.exp_pos _) (Real.log_pos (by norm_num)))]
  norm_num
  ring

/-- The principal Fabius Lambert phase is strictly convex on the whole
half-line ending at the profile peak. -/
theorem strictConvexOn_fabiusPrincipalLambertPhase :
    StrictConvexOn ℝ (Iic (Real.exp (-1) / Real.log 2))
      fabiusPrincipalLambertPhase := by
  apply strictConvexOn_of_deriv2_pos (convex_Iic _)
  · exact fabiusPrincipalLambertPhase_continuousOn_Iic
  · intro x hx
    rw [interior_Iic] at hx
    show 0 < deriv (deriv fabiusPrincipalLambertPhase) x
    exact deriv_deriv_fabiusPrincipalLambertPhase_pos hx

end

end Fabius
