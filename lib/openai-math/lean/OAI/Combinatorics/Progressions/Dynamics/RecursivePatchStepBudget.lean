import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem recursive_patch_step_rank_bound {s d₀ d D E detector j : ℕ}
    (hD : D ≤ d) (hE : E ≤ d₀ + s * (d - D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) :
    detector + E ≤ d₀ + s * d := by
  have hd : detector ≤ s * D := hdetector.trans (Nat.mul_le_mul_right D hj)
  calc
    detector + E ≤ s * D + (d₀ + s * (d - D)) := Nat.add_le_add hd hE
    _ = d₀ + s * ((d - D) + D) := by ring
    _ = d₀ + s * d := by rw [Nat.sub_add_cancel hD]

end Erdos3

end

end OAI
