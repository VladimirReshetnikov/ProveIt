import GowersSzemeredi.Proofs13FiniteCoefficientBounds
import GowersSzemeredi.Proofs13FiniteFloorBudgets

/-! All row-extraction integer budgets above the singleton scale, with no
asymptotic threshold or extra coefficient assumptions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_finite_integer_budgets {alpha : Real} (ha : 0 < alpha) (haone : alpha ≤ 1)
    (N q p L Q : Nat) (hN : 1 ≤ N) (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)))
    (hfloor : IsNatFloor
      (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * q))) p)
    (hL : L = p ∨ L + 1 = p)
    (hQ : (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) / 2 ≤ Q)
    (hlarge : 1 ≤ section13Zeta alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha))) :
    ∃ m : Nat, 0 < m ∧ m * m ≤ N ∧ m + 1 ≤ Q ∧
      section13Zeta alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q alpha)) ≤ m ∧
      (L : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * q))) ≤
        section10Zeta (alpha ^ 32 / 16) / m := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  let c := section13Zeta alpha / 2
  let d := section13ThetaOne theta / (64 * Real.pi)
  let z := section10Zeta (alpha ^ 32 / 16)
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q alpha)
  let u := section13ThetaOne theta ^ 2 / (16 * (q : Real))
  let v := (1 : Real) / (2 : Real) ^ (12 * q)
  let w := (1 : Real) / (2 : Real) ^ (11 * q)
  have hqpos : (0 : Real) < q := by exact_mod_cast hq
  have htheta : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hthetaOne : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hk : 0 < section10SpectrumParameter (alpha ^ 32 / 16) := by
    apply Nat.one_le_ceil_iff.mpr
    unfold section10SpectrumBound
    positivity
  have hz : 0 < z := by
    dsimp [z, section10Zeta]
    exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by positivity))
      (by exact_mod_cast hk)
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hvone : v ≤ 1 := by
    dsimp [v]
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hwone : w ≤ 1 := by
    dsimp [w]
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hcsmall : 2 * c ≤ 1 := by
    have h := section13Zeta_le_one ha haone
    dsimp [c]
    linarith only [h]
  have hdsmall : d ≤ 2 := (section13_initial_coefficient_le_one ha haone).trans (by norm_num)
  have hQbig : 2 ≤ section13Q alpha := by
    have hqone : (1 : Real) ≤ q := by exact_mod_cast hq
    have h := hqBound.trans (section13_qBound_le_half_Q ha haone)
    linarith only [hqone, h]
  have hsquare : 2 * e ≤ 1 := by
    have hp : (2 : Real) ≤ (2 : Real) ^ (13 * section13Q alpha) := by
      calc
        _ = (2 : Real) ^ (1 : Real) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hQbig])
    dsimp [e]
    rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr hp
  have hrec : 2 * e ≤ u * v := (section13_double_recurrence_exponent_margin ha haone hq hqBound).le
  have hvw : v ≤ w := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega : 11 * q ≤ 12 * q)
  have hbohr : 2 * e ≤ u * w := hrec.trans (mul_le_mul_of_nonneg_left hvw hu.le)
  obtain ⟨hrecCoeff, hbohrCoeff⟩ := section13_finite_coefficient_reserves ha haone
  exact finite_floor_row_budgets hc hd hz hu hv hvone hw hwone hcsmall hdsmall
    hsquare hrec hbohr hrecCoeff hbohrCoeff N p L Q hN hlarge hfloor hL hQ

end LeanProofs.GowersSzemeredi
