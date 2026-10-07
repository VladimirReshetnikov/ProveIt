import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3

theorem relative_actual_rank_reconstruction_le
    {s d d₀ old removed : ℕ} (hremoved : removed ≤ old)
    (hreturned : d ≤ d₀ + s * (old - removed)) :
    d + s * removed ≤ d₀ + s * old := by
  calc
    d + s * removed ≤ d₀ + s * (old - removed) + s * removed :=
      Nat.add_le_add_right hreturned _
    _ = d₀ + s * old := by
      rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hremoved]

theorem relative_actual_rank_reconstruction_budget
    {s d removed bound : ℕ} {childCost p : ℝ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min bound ⌊childCost⌋₊)
    (hremoved : (removed : ℝ) ≤ p) :
    ((d + s * removed : ℕ) : ℝ) ≤ childCost + (s : ℝ) * p := by
  have hdim : (d : ℝ) ≤ childCost :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans (Nat.floor_le hchild)
  simpa only [Nat.cast_add, Nat.cast_mul] using
    add_le_add hdim (mul_le_mul_of_nonneg_left hremoved (Nat.cast_nonneg s))

end Erdos3

end

end OAI
