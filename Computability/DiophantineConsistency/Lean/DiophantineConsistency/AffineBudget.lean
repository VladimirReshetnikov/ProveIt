import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Std.Tactic

namespace DiophantineConsistency.AffineBudget
open scoped BigOperators

/-- Spend constructor overhead from the six depth credits per added witness. -/
theorem compose {ι : Type*} [Fintype ι] {C w₀ d₀ extra overhead W D : ℕ}
    (w d : ι → ℕ) (hC : 1 ≤ C)
    (h₀ : d₀ ≤ 6 * w₀ + C) (hd : ∀ i, d i ≤ 6 * w i + C)
    (rule : ∀ h, 1 ≤ h → d₀ ≤ h → (∀ i, d i ≤ h) → D ≤ overhead + h)
    (pay : overhead ≤ 6 * extra) (count : extra + (w₀ + ∑ i, w i) ≤ W) :
    D ≤ 6 * W + C := by
  have hi (i) : w i ≤ w₀ + ∑ j, w j :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  have hb := rule (6 * (w₀ + ∑ i, w i) + C) (by omega) (by omega)
    (fun i => by have := hd i; have := hi i; omega)
  omega

end DiophantineConsistency.AffineBudget
