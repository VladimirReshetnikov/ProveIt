import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integer slack certificate, with no sign split and no nonlinear tactic. -/
namespace AdditionalSimplifications

theorem square_pred_slack_original (z : ℤ) :
    z ≠ 0 ↔ ∃ w : Fin 1 → ℕ, z * z - 1 - (w 0 : ℤ) = 0 := by
  constructor
  · intro hz
    have hs : 1 ≤ z * z := by
      have h : z ≤ -1 ∨ 1 ≤ z := by omega
      rcases h with h | h <;> nlinarith
    refine ⟨fun _ => (z * z - 1).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ z * z - 1)]
    ring
  · rintro ⟨w, hw⟩ hz
    have := Int.natCast_nonneg (w 0)
    rw [hz] at hw
    omega

theorem square_pred_slack (z : ℤ) :
    z ≠ 0 ↔ ∃ w : Fin 1 → ℕ, z * z - 1 - (w 0 : ℤ) = 0 := by
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le
      (Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr (mul_self_pos.mpr hz)))
    exact ⟨fun _ => n, sub_eq_zero.mpr hn⟩
  · rintro ⟨w, hw⟩
    apply mul_self_pos.mp
    have := Int.natCast_nonneg (w 0)
    omega

#print axioms square_pred_slack_original
#print axioms square_pred_slack

end AdditionalSimplifications
