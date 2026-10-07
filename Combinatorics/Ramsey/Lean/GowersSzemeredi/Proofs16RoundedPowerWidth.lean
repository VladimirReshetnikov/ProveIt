import GowersSzemeredi.Proofs16LiftWidth
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! Absorb the floor, square root, and constant losses in the Section 16
affine lift into a positive power, with an explicit starting width. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16RoundedExponentThreshold (z e a b : Real) : Real :=
  max (positivePowerThreshold 16 z e)
    (positivePowerThreshold 1 (((z / 16) ^ (a / 2)) / 4) (e * a / 2 - b))

def section16RoundedPowerThreshold (z e a : Real) : Real :=
  section16RoundedExponentThreshold z e a (e * a / 4)

/-- A lower bound l>=z*m^e gives a pure power after all the lift's rounding
losses. The exponent a may itself have been replaced by a uniform lower
bound; the threshold also guarantees the rounded base is at least one. -/
theorem section16_rounded_power_width_of_exponent {m : Nat} {l z e a b : Real}
    (hz : 0 < z) (he : 0 < e) (ha : 0 < a)
    (hb : b < e * a / 2)
    (hl : z * (m : Real) ^ e ≤ l)
    (hm : section16RoundedExponentThreshold z e a b ≤ (m : Real)) :
    1 ≤ (Nat.floor l : Real) / 8 ∧
      (m : Real) ^ b ≤ Real.sqrt (((Nat.floor l : Real) / 8) ^ a) / 4 := by
  have hm0 : (0 : Real) < m := (zero_lt_one.trans_le
    (positivePowerThreshold_one_le 16 z e)).trans_le ((le_max_left _ _).trans hm)
  have hl16 : 16 ≤ l :=
    (positivePowerThreshold_spec hz he ((le_max_left _ _).trans hm)).trans hl
  obtain ⟨_, hfloor⟩ := floor_half_lower (show 2 ≤ l by linarith only [hl16])
  have hbase : (z / 16) * (m : Real) ^ e ≤ (Nat.floor l : Real) / 8 := by
    linarith only [hl, hfloor]
  have hbase1 : 1 ≤ (Nat.floor l : Real) / 8 := by linarith only [hl16, hfloor]
  refine ⟨hbase1, ?_⟩
  let D := ((z / 16) ^ (a / 2)) / 4
  let gap := e * a / 2 - b
  have hD : 0 < D := by dsimp [D]; positivity
  have hgap : 0 < gap := sub_pos.mpr hb
  have hlarge : 1 ≤ D * (m : Real) ^ gap :=
    positivePowerThreshold_spec hD hgap ((le_max_right _ _).trans hm)
  have hpow : (m : Real) ^ b * (m : Real) ^ gap = (m : Real) ^ (e * (a / 2)) := by
    rw [← Real.rpow_add hm0]
    congr 1
    dsimp [gap]
    ring
  calc
    (m : Real) ^ b ≤ (m : Real) ^ b * (D * (m : Real) ^ gap) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hm0.le b)
    _ = D * (m : Real) ^ (e * (a / 2)) := by rw [← hpow]; ring
    _ = Real.sqrt (((z / 16) * (m : Real) ^ e) ^ a) / 4 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ (z / 16) * (m : Real) ^ e),
        Real.mul_rpow (by positivity : 0 ≤ z / 16) (Real.rpow_nonneg hm0.le _),
        ← Real.rpow_mul hm0.le]
      rw [show a * (1 / 2 : Real) = a / 2 by ring]
      dsimp [D]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt (Real.rpow_le_rpow (by positivity) hbase ha.le)) (by norm_num)

/-- A convenient fixed choice retains half of the limiting exponent.
The preceding theorem permits any exponent strictly below e*a/2. -/
theorem section16_rounded_power_width {m : Nat} {l z e a : Real}
    (hz : 0 < z) (he : 0 < e) (ha : 0 < a)
    (hl : z * (m : Real) ^ e ≤ l)
    (hm : section16RoundedPowerThreshold z e a ≤ (m : Real)) :
    1 ≤ (Nat.floor l : Real) / 8 ∧
      (m : Real) ^ (e * a / 4) ≤ Real.sqrt (((Nat.floor l : Real) / 8) ^ a) / 4 :=
  section16_rounded_power_width_of_exponent hz he ha (by nlinarith only [mul_pos he ha]) hl hm

end LeanProofs.GowersSzemeredi
