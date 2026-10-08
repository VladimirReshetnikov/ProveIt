import GowersSzemeredi.Proofs16CubicRelationDecomposition
import GowersSzemeredi.Proofs16CommonBasePieceBudget

/-! A concrete nonunit parameter fits the mass budget of cubic extraction.
The remaining obligation is to compare the cubic cover controls against
MultiplyLinear at this parameter; no such comparison is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Halving the outer density costs at most a square of its iteration budget. -/
theorem multipleS_half_le_square {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    multipleS (theta / 2) gamma k ≤ (multipleS theta gamma k)^2 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  have hbase : 2 / (theta / 2 * gamma) ≤ (2 / (theta * gamma))^2 := by
    calc
      _ = 2 * (2 / (theta * gamma)) := by ring
      _ ≤ (2 / (theta * gamma)) * (2 / (theta * gamma)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  unfold multipleS
  calc
    _ ≤ ((2 / (theta * gamma))^2)^((2 : Nat)^((2 : Nat)^(k+6))) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Advancing a dimension absorbs a fixed power of the previous budget. -/
theorem multipleS_pow_le_succ {theta gamma : Real} (k n : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hn : n ≤ (2 : Nat)^((2 : Nat)^(k+6))) :
    (multipleS theta gamma k)^n ≤ multipleS theta gamma (k+1) := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (1 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  unfold multipleS
  rw [← pow_mul]
  apply pow_le_pow_right₀ hb
  calc
    (2 : Nat)^(2^(k+6)) * n ≤ 2^(2^(k+6)) * 2^(2^(k+6)) := Nat.mul_le_mul_left _ hn
    _ = 2^(2^(k+1+6)) := by
      rw [← pow_add]
      congr 1
      rw [show k+1+6 = (k+6)+1 by omega, pow_succ (2 : Nat) (k+6)]
      omega

/-- The retained mass can pay for S(theta,gamma,1)^8 while staying inside
the source's dimension-two total iteration budget. -/
theorem section16_cubic_piece_parameter_budget {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    1 ≤ (multipleS theta gamma 1)^8 ∧
      (multipleS theta gamma 1)^8 ≤ section16CubicPieceMass theta gamma * multipleS theta gamma 2 := by
  have hS : 1 ≤ multipleS theta gamma 1 := one_le_multipleS 1 ht ht1 hg hg1
  have hη := section16CubicPieceMass_pos ht hg
  have hinv : (section16CubicPieceMass theta gamma)⁻¹ ≤ (multipleS theta gamma 1)^2 := by
    exact (section16_thetaTwo_inverse_le_iteration 1 (by positivity : 0 < theta / 2)
      (by linarith) hg hg1).trans (multipleS_half_le_square 1 ht ht1 hg hg1)
  have hmass : 1 ≤ section16CubicPieceMass theta gamma * (multipleS theta gamma 1)^2 := by
    have hh := mul_le_mul_of_nonneg_left hinv hη.le
    simpa only [mul_inv_cancel₀ hη.ne'] using hh
  have hpower := multipleS_pow_le_succ 1 10 ht ht1 hg hg1 (by norm_num)
  refine ⟨one_le_pow₀ hS, ?_⟩
  calc
    (multipleS theta gamma 1)^8 = 1 * (multipleS theta gamma 1)^8 := by ring
    _ ≤ (section16CubicPieceMass theta gamma * (multipleS theta gamma 1)^2) *
        (multipleS theta gamma 1)^8 := mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = section16CubicPieceMass theta gamma * (multipleS theta gamma 1)^10 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower hη.le

end LeanProofs.GowersSzemeredi
