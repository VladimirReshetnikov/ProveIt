import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

theorem eq_zero_of_mem_realDenominatorGrid_of_abs_lt {ι : Type*} {l : ℕ}
    (hl : 0 < l) {v : ι → ℝ} (hv : v ∈ realDenominatorGrid l)
    (hsmall : ∀ i, |v i| < 1 / (l : ℝ)) : v = 0 := by
  obtain ⟨z, hz⟩ := hv
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  funext i
  have hzi : (z i : ℝ) = (l : ℝ) * v i := congrFun hz i
  have habs : |(z i : ℝ)| < 1 := by
    rw [hzi, abs_mul, abs_of_pos hl']
    simpa only [mul_comm] using (lt_div_iff₀ hl').mp (hsmall i)
  have hz0 : z i = 0 := by
    have h : |z i| < (1 : ℤ) := by exact_mod_cast habs
    have := abs_lt.mp h
    omega
  have hv0 : (l : ℝ) * v i = 0 := by simpa only [hz0, Int.cast_zero] using hzi.symm
  exact (mul_eq_zero.mp hv0).resolve_left hl'.ne'

theorem exists_large_coordinate_of_mem_realDenominatorGrid {ι : Type*} {l : ℕ}
    (hl : 0 < l) {v : ι → ℝ} (hv : v ∈ realDenominatorGrid l) (hne : v ≠ 0) :
    ∃ i, 1 / (l : ℝ) ≤ |v i| := by
  by_contra! h
  exact hne (eq_zero_of_mem_realDenominatorGrid_of_abs_lt hl hv h)

end Erdos3

end

end OAI
