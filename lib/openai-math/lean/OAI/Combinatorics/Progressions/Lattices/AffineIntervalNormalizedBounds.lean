import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem affineInterval_normalized_bounds
    {L H step : ℕ} {start : ℤ}
    (hL : 0 < L) (hH : 2 ≤ H) (hstep : 0 < step)
    (hinside : ∀ t : Fin H, 0 ≤ start + step * (t.val : ℤ) ∧
      start + step * (t.val : ℤ) < L) :
    0 ≤ (start : ℝ) / L ∧
      0 < (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L ∧
      (start : ℝ) / L + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L < 1 ∧
      (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L ≤ 1 := by
  have hHpos : 0 < H := by omega
  have hlast : H - 1 < H := Nat.sub_lt hHpos (by norm_num)
  have hstartZ : 0 ≤ start := by
    simpa only [Nat.cast_zero, mul_zero, add_zero] using (hinside ⟨0, hHpos⟩).1
  have hendZ := (hinside ⟨H - 1, hlast⟩).2
  have hstart : (0 : ℝ) ≤ start := by exact_mod_cast hstartZ
  have hend : (start : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by
    exact_mod_cast hendZ
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hstepreal : (0 : ℝ) < step := by exact_mod_cast hstep
  have hHreal : (0 : ℝ) < ((H - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < H - 1 by omega)
  have hlower := div_nonneg hstart hLreal.le
  have hwidth := div_pos (mul_pos hstepreal hHreal) hLreal
  have hsum : (start : ℝ) / L + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L < 1 := by
    rw [← add_div]
    exact (div_lt_one hLreal).mpr hend
  exact ⟨hlower, hwidth, hsum, by linarith⟩

end Erdos3

end

end OAI
