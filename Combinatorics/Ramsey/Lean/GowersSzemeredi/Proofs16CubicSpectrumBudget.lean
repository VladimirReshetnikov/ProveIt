import GowersSzemeredi.Proofs16BaseFamilyPowerBound
import GowersSzemeredi.Proofs16CubicPieceParameterBudget

/-! The fixed dimension-two spectrum family is bounded by the previous
source iteration scale. This keeps its recurrence loss independent of the
inner cover loss, with an explicit outer-parameter budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multipleS_two_le {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    2 ≤ multipleS theta gamma k := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  calc
    2 ≤ 2 / (theta * gamma) := hb
    _ = (2 / (theta * gamma))^1 := by simp
    _ ≤ _ := pow_le_pow_right₀ (by linarith : (1 : Real) ≤ 2 / (theta * gamma))
      (by have hh : 0 < (2 : Nat)^((2 : Nat)^(k+6)) := by positivity
          omega)

theorem section16ThetaOne_one_inverse_le_square {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (section16ThetaOne theta gamma 1)⁻¹ ≤ (multipleS theta gamma 0)^2 := by
  have heq : (section16ThetaOne theta gamma 1)⁻¹ = multipleS (theta / 2) gamma 0 := by
    unfold section16ThetaOne multipleS
    rw [← inv_pow]
    congr 1
    ring
  rw [heq]
  exact multipleS_half_le_square 0 ht ht1 hg hg1

/-- The loss-independent spectrum graph count fits the first-dimensional
source scale, without invoking the source's spectrum graph-count bound. -/
theorem section16CubicSpectrumCount_le_iteration {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (section16CubicSpectrumCount theta gamma : Real) ≤ multipleS theta gamma 1 := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  let a := section16ThetaOne theta gamma 1
  let d := section16Delta a
  let S := multipleS theta gamma 0
  have ha' : 0 < a := ha
  have hd' : 0 < d := hd
  have hS : 2 ≤ S := multipleS_two_le 0 ht ht1 hg hg1
  have hS0 : 0 ≤ S := by linarith
  have hinv : a⁻¹ ≤ S^2 := section16ThetaOne_one_inverse_le_square ht ht1 hg hg1
  have hdelta : a^6 / (2 : Real)^(37 : Nat) / (4 : Real)^(6 : Nat) ≤ d := by
    have hh := Real.rpow_le_rpow_of_exponent_ge (by positivity : 0 < a / 4)
      (by dsimp [a]; linarith : a / 4 ≤ 1) (by norm_num : (11 : Real) / 2 ≤ (6 : Real))
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (2 : Real)^(-(37 : Real)))
    dsimp [d, section16Delta]
    rw [Real.rpow_ofNat, div_pow] at hm
    simpa [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hm
  have hDlow : a^7 / (2 : Real)^(52 : Nat) ≤ d * (a / 8) := by
    calc
      a^7 / (2 : Real)^(52 : Nat) = (a^6 / (2 : Real)^37 / (4 : Real)^6) * (a / 8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdelta (by positivity)
  have hratio : 2 / (d * (a / 8)) ≤ (2 : Real)^(53 : Nat) * (a⁻¹)^7 := by
    apply (div_le_iff₀ (by positivity : 0 < d * (a / 8))).mpr
    calc
      2 = ((2 : Real)^(53 : Nat) * (a⁻¹)^7) * (a^7 / (2 : Real)^(52 : Nat)) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hDlow (by positivity)
  have hratioS : 2 / (d * (a / 8)) ≤ S^67 := by
    calc
      _ ≤ (2 : Real)^(53 : Nat) * (a⁻¹)^7 := hratio
      _ ≤ S^53 * (S^2)^7 := mul_le_mul
        (pow_le_pow_left₀ (by norm_num) hS 53)
        (pow_le_pow_left₀ (inv_nonneg.mpr ha'.le) hinv 7)
        (pow_nonneg (inv_nonneg.mpr ha'.le) _) (pow_nonneg hS0 _)
      _ = _ := by ring
  calc
    (section16CubicSpectrumCount theta gamma : Real) ≤ (2 / (d * (a / 8)))^(10002 : Nat) :=
      section16BaseFamilyBound_le_power hd hd1 (by positivity) (by linarith)
    _ ≤ (S^67)^(10002 : Nat) := pow_le_pow_left₀ (by positivity) hratioS _
    _ = S^670134 := by rw [← pow_mul]
    _ ≤ multipleS theta gamma 1 := multipleS_pow_le_succ 0 670134 ht ht1 hg hg1 (by norm_num)

end LeanProofs.GowersSzemeredi
