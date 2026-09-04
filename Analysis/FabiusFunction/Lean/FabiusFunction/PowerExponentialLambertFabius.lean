import FabiusFunction.GeneralizedLambertCoordinate
import FabiusFunction.PowerExponentialLambertAsymptotics
import FabiusFunction.FabiusLambertSaddle

/-!
# Bridges from scaled Lambert phases to the Fabius saddle coordinates

The generic two-branch inverse in `PowerExponentialLambert.lean` contains two
previously separate constructions in this corpus:

* at rate `beta = 1`, its lower branch is
  `generalizedLambertCoordinate`;
* at power `m = 1`, amplitude `A = 1`, and rate `beta = log 2`, its lower
  branch is the exact Fabius phase `fabiusLambertPhase`.

The bridge supplies both an interior argument theorem that discharges the
natural Lambert-domain premise of the older generalized saddle theorem and
an endpoint-inclusive replacement based on the generic closed-branch solve
law.  It also exports the principal Fabius phase, the exact two-root
classification on the nonnegative half-line, endpoint-inclusive continuity,
the principal small-input equivalence, and the exact two-sided
inversion of the Fabius saddle map by the lower phase
(`fabiusLambertPhase_invOn`).  No new branch choice or analytic
assumption is introduced.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

noncomputable section

/-- At unit exponential rate, the generic lower phase is exactly the
previously defined generalized Lambert coordinate. -/
theorem lowerPowerExponentialPhase_rate_one
    (m : ℕ) (C p x : ℝ) :
    lowerPowerExponentialPhase m (C * p) 1 x =
      generalizedLambertCoordinate m C p x := by
  unfold lowerPowerExponentialPhase powerExponentialLambertArgument
    generalizedLambertCoordinate
  simp only [div_one, one_div]
  have harg : -((m : ℝ)⁻¹ * (x / (C * p)) ^ ((m : ℝ)⁻¹)) =
      -((x / (C * p)) ^ ((m : ℝ)⁻¹) / (m : ℝ)) := by
    rw [div_eq_mul_inv]
    ring
  rw [harg]

/-- Positivity and the intrinsic peak interval automatically place the
generalized Lambert argument in the full closed-left lower-branch domain. -/
theorem generalizedLambertCoordinate_argument_mem_Ico
    {m : ℕ} (hm : m ≠ 0) {C p x : ℝ} (hCp : 0 < C * p)
    (hx : x ∈ Ioc 0 (powerExponentialPeak m (C * p) 1)) :
    -((x / (C * p)) ^ ((m : ℝ)⁻¹) / (m : ℝ)) ∈
      Ico (-Real.exp (-1)) 0 := by
  have hmem := powerExponentialLambertArgument_mem_Ico hm hCp zero_lt_one hx
  have harg : powerExponentialLambertArgument m (C * p) 1 x =
      -((x / (C * p)) ^ ((m : ℝ)⁻¹) / (m : ℝ)) := by
    unfold powerExponentialLambertArgument
    rw [one_div, div_eq_mul_inv]
    ring
  rw [← harg]
  exact hmem

/-- Strictly below the profile peak, the generalized Lambert argument lies
in the open domain required by the older generalized saddle theorem. -/
theorem generalizedLambertCoordinate_argument_mem_Ioo
    {m : ℕ} (hm : m ≠ 0) {C p x : ℝ} (hCp : 0 < C * p)
    (hx : x ∈ Ioo 0 (powerExponentialPeak m (C * p) 1)) :
    -((x / (C * p)) ^ ((m : ℝ)⁻¹) / (m : ℝ)) ∈
      Ioo (-Real.exp (-1)) 0 := by
  have hmem := powerExponentialLambertArgument_mem_Ioo hm hCp zero_lt_one hx
  have harg : powerExponentialLambertArgument m (C * p) 1 x =
      -((x / (C * p)) ^ ((m : ℝ)⁻¹) / (m : ℝ)) := by
    unfold powerExponentialLambertArgument
    rw [one_div, div_eq_mul_inv]
    ring
  rw [← harg]
  exact hmem

/-- The generalized lower-Lambert coordinate solves its saddle equation on
the intrinsic positive interval through the profile peak.  This
endpoint-inclusive replacement uses the generic closed lower-branch solve
law; the separate open-domain lemma above directly supplies the older
theorem's premise away from the peak. -/
theorem generalizedLambertCoordinate_solves_saddle_of_mem
    {m : ℕ} (hm : m ≠ 0) {C p x : ℝ} (hCp : 0 < C * p)
    (hx : x ∈ Ioc 0 (powerExponentialPeak m (C * p) 1)) :
    C * p * generalizedLambertCoordinate m C p x ^ m *
        Real.exp (-generalizedLambertCoordinate m C p x) = x := by
  have hsolve := lowerPowerExponentialPhase_solves hm hCp zero_lt_one hx
  rw [lowerPowerExponentialPhase_rate_one] at hsolve
  simpa [powerExponentialSaddle] using hsolve

/-- At power one, amplitude one, and rate `log 2`, the generic profile is
the Fabius saddle map `lambda * 2 ^ (-lambda)`. -/
theorem powerExponentialSaddle_one_one_log_two (lambda : ℝ) :
    powerExponentialSaddle 1 1 (Real.log 2) lambda =
      lambda * (2 : ℝ) ^ (-lambda) := by
  unfold powerExponentialSaddle
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The generic peak specializes to the classical Fabius turning value
`exp (-1) / log 2`. -/
theorem powerExponentialPeak_one_one_log_two :
    powerExponentialPeak 1 1 (Real.log 2) =
      Real.exp (-1) / Real.log 2 := by
  rw [powerExponentialPeak]
  norm_num
  ring

/-- The generic lower inverse branch specializes exactly to the Fabius
lower-Lambert phase. -/
theorem lowerPowerExponentialPhase_one_one_log_two (x : ℝ) :
    lowerPowerExponentialPhase 1 1 (Real.log 2) x =
      fabiusLambertPhase x := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold lowerPowerExponentialPhase powerExponentialLambertArgument
    fabiusLambertPhase paperLambertN
  simp only [Nat.cast_one, inv_one, div_one, Real.rpow_one]
  change -(1 / Real.log 2) *
      lowerLambertW (-(Real.log 2 * x)) =
    -lowerLambertW (-(Real.log 2 * x)) / Real.log 2
  field_simp [hlog]

/-- The principal nonnegative inverse of the classical Fabius saddle map. -/
noncomputable def fabiusPrincipalLambertPhase (x : ℝ) : ℝ :=
  principalPowerExponentialPhase 1 1 (Real.log 2) x

/-- Every nonnegative solution of the classical Fabius saddle equation is
one of its principal or lower Lambert phases.  At the turning value the two
alternatives coincide. -/
theorem fabiusSaddle_eq_iff_eq_principal_or_eq_lower
    {x lambda : ℝ}
    (hx : x ∈ Ioc 0 (Real.exp (-1) / Real.log 2))
    (hlambda : 0 ≤ lambda) :
    lambda * (2 : ℝ) ^ (-lambda) = x ↔
      lambda = fabiusPrincipalLambertPhase x ∨
        lambda = fabiusLambertPhase x := by
  have hx' : x ∈ Ioc 0
      (powerExponentialPeak 1 1 (Real.log 2)) := by
    rwa [powerExponentialPeak_one_one_log_two]
  simpa only [powerExponentialSaddle_one_one_log_two,
    fabiusPrincipalLambertPhase,
    lowerPowerExponentialPhase_one_one_log_two] using
      (powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower
        (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
        (x := x) (lambda := lambda) zero_lt_one
        (Real.log_pos (by norm_num)) hx' hlambda)

/-- Strictly below the classical turning value, the two nonnegative Fabius
saddle roots are distinct. -/
theorem fabiusPrincipalLambertPhase_ne_fabiusLambertPhase
    {x : ℝ} (hx : x ∈ Ioo 0 (Real.exp (-1) / Real.log 2)) :
    fabiusPrincipalLambertPhase x ≠ fabiusLambertPhase x := by
  have hx' : x ∈ Ioo 0
      (powerExponentialPeak 1 1 (Real.log 2)) := by
    rwa [powerExponentialPeak_one_one_log_two]
  simpa only [fabiusPrincipalLambertPhase,
    lowerPowerExponentialPhase_one_one_log_two] using
      (principalPowerExponentialPhase_ne_lowerPowerExponentialPhase
        (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
        zero_lt_one (Real.log_pos (by norm_num)) hx')

/-! ## Exact inversion of the classical Fabius saddle map -/

/-- **Two-sided inversion.**  The lower Fabius phase and the saddle map
`lambda ↦ lambda * 2 ^ (-lambda)` are exact setwise inverses between
`[1 / log 2, ∞)` and the positive endpoint-inclusive profile-value
interval `(0, exp (-1) / log 2]`.  This is the
`(m, A, beta) = (1, 1, log 2)` instance of
`lowerPowerExponentialPhase_invOn`. -/
theorem fabiusLambertPhase_invOn :
    InvOn fabiusLambertPhase (fun lam : ℝ ↦ lam * (2 : ℝ) ^ (-lam))
      (Ici (Real.log 2)⁻¹) (Ioc 0 (Real.exp (-1) / Real.log 2)) := by
  have h := lowerPowerExponentialPhase_invOn
    (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
    zero_lt_one (Real.log_pos (by norm_num))
  have hphase : lowerPowerExponentialPhase 1 1 (Real.log 2) =
      fabiusLambertPhase :=
    funext lowerPowerExponentialPhase_one_one_log_two
  have hsaddle : powerExponentialSaddle 1 1 (Real.log 2) =
      (fun lam : ℝ ↦ lam * (2 : ℝ) ^ (-lam)) :=
    funext powerExponentialSaddle_one_one_log_two
  simpa only [hphase, hsaddle, powerExponentialPeak_one_one_log_two,
    Nat.cast_one, one_div] using h

/-- On `[1 / log 2, ∞)` the lower Fabius phase inverts the saddle map
pointwise: `fabiusLambertPhase (lam * 2 ^ (-lam)) = lam`. -/
theorem fabiusLambertPhase_leftInv {lam : ℝ}
    (h : (Real.log 2)⁻¹ ≤ lam) :
    fabiusLambertPhase (lam * (2 : ℝ) ^ (-lam)) = lam :=
  fabiusLambertPhase_invOn.1 (mem_Ici.mpr h)

/-- On `(0, exp (-1) / log 2]` the saddle map inverts the lower Fabius
phase pointwise:
`fabiusLambertPhase x * 2 ^ (-fabiusLambertPhase x) = x`. -/
theorem fabiusLambertPhase_rightInv {x : ℝ}
    (hx : x ∈ Ioc 0 (Real.exp (-1) / Real.log 2)) :
    fabiusLambertPhase x * (2 : ℝ) ^ (-fabiusLambertPhase x) = x :=
  fabiusLambertPhase_invOn.2 hx

/-- The principal Fabius saddle phase is continuous on the full closed
profile-value interval. -/
theorem fabiusPrincipalLambertPhase_continuousOn_Icc :
    ContinuousOn fabiusPrincipalLambertPhase
      (Icc 0 (Real.exp (-1) / Real.log 2)) := by
  change ContinuousOn
    (principalPowerExponentialPhase 1 1 (Real.log 2))
      (Icc 0 (Real.exp (-1) / Real.log 2))
  simpa only [powerExponentialPeak_one_one_log_two] using
      (principalPowerExponentialPhase_continuousOn_Icc
        (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
        zero_lt_one (Real.log_pos (by norm_num)))

/-- The lower Fabius saddle phase is continuous through its finite branch
point on the positive endpoint-inclusive interval. -/
theorem fabiusLambertPhase_continuousOn_Ioc :
    ContinuousOn fabiusLambertPhase
      (Ioc 0 (Real.exp (-1) / Real.log 2)) := by
  have h := lowerPowerExponentialPhase_continuousOn_Ioc
    (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
    zero_lt_one (Real.log_pos (by norm_num))
  rw [powerExponentialPeak_one_one_log_two] at h
  have hfun : lowerPowerExponentialPhase 1 1 (Real.log 2) =
      fabiusLambertPhase := by
    funext x
    exact lowerPowerExponentialPhase_one_one_log_two x
  rwa [hfun] at h

/-- Near zero, the principal Fabius saddle phase is asymptotic to the input
itself. -/
theorem fabiusPrincipalLambertPhase_isEquivalent_id :
    (fun x : ℝ ↦ fabiusPrincipalLambertPhase x)
      ~[nhdsWithin 0 (Ioi 0)] (fun x : ℝ ↦ x) := by
  simpa only [fabiusPrincipalLambertPhase, Nat.cast_one, inv_one, div_one,
    Real.rpow_one] using
      (principalPowerExponentialPhase_isEquivalent_rpow
        (m := 1) one_ne_zero (A := 1) (beta := Real.log 2)
        zero_lt_one (Real.log_pos (by norm_num)))

end

end Fabius
