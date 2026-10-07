import GowersSzemeredi.Proofs16UnusedCoordinateLift
import GowersSzemeredi.Proofs16UniformFaceParameter

/-! The genuine proper-face iteration parameter has enough reserve for the
all-scale unused-coordinate extension, in every intermediate dimension. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multipleS_ge_coarse_graph_count (k : Nat) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ((3 ^ (k + 2) : Nat) : Real) ≤ multipleS theta gamma k := by
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := by
    apply (le_div_iff₀ (mul_pos ht hg)).mpr
    have h := mul_le_one₀ ht1 hg.le hg1
    linarith
  have hexp : 2 * (k + 2) ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) := by
    have hk : k + 2 ≤ (2 : Nat) ^ (k + 1) := Nat.lt_two_pow_self
    have hinner : k + 2 ≤ (2 : Nat) ^ (k + 6) := by
      have hh : k + 7 ≤ (2 : Nat) ^ (k + 6) := Nat.lt_two_pow_self
      omega
    calc
      2 * (k + 2) ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 hk
      _ = 2 ^ (k + 2) := by rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hinner
  calc
    _ = (3 : Real) ^ (k + 2) := by push_cast; rfl
    _ ≤ (4 : Real) ^ (k + 2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (2 : Real) ^ (2 * (k + 2)) := by rw [pow_mul]; norm_num
    _ ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := pow_le_pow_right₀ (by norm_num) hexp
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) hb _

/-- This is the parameter supplied by the structured-pair construction,
with enough reserve for every lift up to its ambient dimension. -/
theorem section16_face_parameter_lift_reserve (k : Nat) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    2 ≤ gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k ∧
    ∀ l ≤ k + 1, ((3 ^ l : Nat) : Real) ≤
      gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k := by
  obtain ⟨heps, heps1⟩ := section16_face_error_range k ht ht1
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hcount := multipleS_ge_coarse_graph_count k heps heps1 hg hg1
  have hS : 0 ≤ multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k :=
    (one_le_multipleS k heps heps1 hg hg1).trans' (by norm_num)
  have hbound := hcount.trans (le_mul_of_one_le_left hS hginv)
  constructor
  · have htwo : (2 : Real) ≤ (3 ^ (k + 2) : Nat) := by
      exact_mod_cast (show (2 : Nat) ≤ 3 ^ (k + 2) from
        (by norm_num : 2 ≤ 3 ^ 1).trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
    exact htwo.trans hbound
  · intro l hl
    have hh : ((3 ^ l : Nat) : Real) ≤ (3 ^ (k + 2) : Nat) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : Nat)) (by omega : l ≤ k + 2))
    exact hh.trans hbound

end LeanProofs.GowersSzemeredi
