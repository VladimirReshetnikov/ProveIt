import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

namespace DiophantineConsistency.NativePellBootstrap

/-- The explicit least positive unit for the native first norm. -/
def firstUnit (Q : ℕ) : Pell.Solution₁ ((Q : ℤ) * (Q + 1)) :=
  Pell.Solution₁.mk (2 * Q + 1) 2 (by ring)

/-- No square lies at `Q(Q+1)+1`, and the next available second coordinate
is two. This proves the ordinary fundamental-unit assertion unboundedly. -/
theorem firstUnit_fundamental {Q : ℕ} (hQ : 0 < Q) :
    Pell.IsFundamental (firstUnit Q) := by
  refine ⟨by change (1 : ℤ) < 2 * Q + 1; omega, by change (0 : ℤ) < 2; norm_num, ?_⟩
  intro b hb
  change (2 * Q + 1 : ℤ) ≤ b.x
  have hQZ : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hprop := b.prop
  have hysq : (4 : ℤ) ≤ b.y ^ 2 := by
    by_contra hlt
    have hsmall : b.y ^ 2 < (2 : ℤ) ^ 2 := by omega
    have habs := abs_lt_of_sq_lt_sq hsmall (by norm_num : (0 : ℤ) ≤ 2)
    have hycases : b.y = -1 ∨ b.y = 0 ∨ b.y = 1 := by
      rw [abs_lt] at habs
      omega
    have hnotone (hy : b.y ^ 2 = 1) : False := by
      have hlow : (Q : ℤ) ^ 2 < b.x ^ 2 := by nlinarith
      have hhigh : b.x ^ 2 < ((Q : ℤ) + 1) ^ 2 := by nlinarith
      have hlo : (Q : ℤ) < b.x := (sq_lt_sq₀ (by positivity) (by omega)).mp hlow
      have hhi : b.x < (Q : ℤ) + 1 := (sq_lt_sq₀ (by omega) (by positivity)).mp hhigh
      omega
    rcases hycases with hy | hy | hy
    · exact hnotone (by rw [hy]; norm_num)
    · have hx2 : (1 : ℤ) < b.x ^ 2 := by
        simpa using (sq_lt_sq₀ (by norm_num : (0 : ℤ) ≤ 1) (by omega)).mpr hb
      rw [hy] at hprop
      norm_num at hprop
      omega
    · exact hnotone (by rw [hy]; norm_num)
  have hxsq : (2 * Q + 1 : ℤ) ^ 2 ≤ b.x ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (Q : ℤ) * (Q + 1) by positivity)
      (show 0 ≤ b.y ^ 2 - 4 by omega)]
  exact (sq_le_sq₀ (by positivity) (by omega)).mp hxsq

end DiophantineConsistency.NativePellBootstrap
