import OAI.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow

namespace OAI

section

namespace Erdos3

theorem naturalScaleIntegerWindow_coordinate_bound {J : Type*} [Fintype J]
    {H : ℝ} (hH : 0 ≤ H) {N : ℕ} (hN : 0 < N)
    {z : J → ℤ} (hz : z ∈ naturalScaleIntegerWindow J H N) (j : J) :
    |(z j : ℝ)| ≤ (H + 1) * N := by
  classical
  have hc := (mem_centeredIntegerBox _ _).mp hz j
  have hc' : |(z j : ℝ)| ≤ (⌈H * (N : ℝ)⌉₊ : ℝ) := by exact_mod_cast hc
  have hr := Nat.ceil_lt_add_one (mul_nonneg hH (Nat.cast_nonneg N))
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

end Erdos3

end

end OAI
