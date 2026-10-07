import GowersSzemeredi.Proofs16LargePieceMass

/-! Keep the actual common-base mass in the extraction budget instead of
weakening it to the reciprocal source iteration count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The piece-count budget obtained by dividing the relation-size bound
by the density actually retained by the common-base construction. -/
def section16CommonBasePieceBound (theta gamma : Real) (k : Nat) : Real :=
  gamma ^ (-(2 : Int)) / section16ThetaTwo (section16ThetaOne theta gamma k)

theorem section16CommonBasePieceBound_pos {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (hg : 0 < gamma) :
    0 < section16CommonBasePieceBound theta gamma k := by
  unfold section16CommonBasePieceBound section16ThetaTwo section16ThetaOne
  positivity

/-- Even the source's preceding-dimensional iteration count bounds the
actual extraction budget. -/
theorem section16CommonBasePieceBound_le_previous_dimension {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16CommonBasePieceBound theta gamma k ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k := by
  unfold section16CommonBasePieceBound
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (section16_thetaTwo_inverse_le_iteration k ht ht1 hg hg1) (by positivity)

theorem multipleS_strictMono_dimension {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    StrictMono (multipleS theta gamma) := by
  intro l k hlk
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hbase : (1 : Real) < 2 / (theta * gamma) := (lt_div_iff₀ htg).mpr (by linarith)
  apply pow_lt_pow_right₀ hbase
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
  omega

/-- The real count budget is strictly smaller than the source count in the
ambient dimension throughout the admissible density range. -/
theorem section16CommonBasePieceBound_lt_source {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16CommonBasePieceBound theta gamma k <
      gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1) := by
  apply (section16CommonBasePieceBound_le_previous_dimension k ht ht1 hg hg1).trans_lt
  exact mul_lt_mul_of_pos_left (multipleS_strictMono_dimension ht ht1 hg hg1 (Nat.lt_succ_self k))
    (by positivity)

/-- Rounding up preserves the non-strict comparison of uniform iteration
counts; strictness is claimed separately for the real budgets. -/
theorem section16CommonBasePieceBound_ceil_le_source {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    Nat.ceil (section16CommonBasePieceBound theta gamma k) ≤
      Nat.ceil (gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1)) :=
  Nat.ceil_mono (section16CommonBasePieceBound_lt_source k ht ht1 hg hg1).le

end LeanProofs.GowersSzemeredi
