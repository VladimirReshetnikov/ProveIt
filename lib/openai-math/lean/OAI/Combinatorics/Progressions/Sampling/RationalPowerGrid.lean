import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

theorem rational_power_clear_denominator (a : ℤ) (d s k : ℕ) (hd : 0 < d) (hk : k ≤ s) :
    (d : ℝ) ^ s * ((a : ℝ) / d) ^ k = (a : ℝ) ^ k * (d : ℝ) ^ (s - k) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℝ) ^ s = (d : ℝ) ^ (s - k) * (d : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hpow, div_pow]
  field_simp

theorem realDenominatorGrid_rational_power_scale {ι : Type*}
    (degree : ι → ℕ) (D d s : ℕ) (a : ℤ) (hd : 0 < d) (hdegree : ∀ i, degree i ≤ s)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid D) :
    (fun i => ((a : ℝ) / d) ^ degree i * x i) ∈ realDenominatorGrid (D * d ^ s) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => a ^ degree i * (d : ℤ) ^ (s - degree i) * z i, ?_⟩
  funext i
  have hi : (z i : ℝ) = (D : ℝ) * x i := congrFun hz i
  change ((a ^ degree i * (d : ℤ) ^ (s - degree i) * z i : ℤ) : ℝ) =
    ((D * d ^ s : ℕ) : ℝ) * (((a : ℝ) / d) ^ degree i * x i)
  push_cast
  rw [hi]
  calc
    _ = (D : ℝ) * ((d : ℝ) ^ s * ((a : ℝ) / d) ^ degree i) * x i := by
      rw [rational_power_clear_denominator a d s (degree i) hd (hdegree i)]
      ring
    _ = _ := by ring

end Erdos3

end

end OAI
