import FabiusFunction.GeneralizedLambertCoordinate
import FabiusFunction.PowerExponentialLambert
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
law.  No new branch choice or analytic assumption is introduced.
-/

set_option autoImplicit false

open Set

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

end

end Fabius
