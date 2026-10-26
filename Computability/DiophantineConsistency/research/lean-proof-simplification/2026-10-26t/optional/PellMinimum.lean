import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace PellMinimum

/-- For positive Pell solutions, minimizing the square of y minimizes x. -/
theorem fundamental_of_minimal_y_sq {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y)
    (hmin : ∀ b : Pell.Solution₁ d, 1 < b.x → a.y ^ 2 ≤ b.y ^ 2) :
    Pell.IsFundamental a := by
  refine ⟨hax, hay, ?_⟩
  intro b hb
  apply (sq_le_sq₀ (by omega : 0 ≤ a.x) (by omega : 0 ≤ b.x)).mp
  rw [a.prop_x, b.prop_x]
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hmin b hb)
      (Pell.Solution₁.d_pos_of_one_lt_x hax).le)

/-- There is no integral square strictly between consecutive nonnegative squares. -/
theorem not_sq_between (n x : ℤ) (hn : 0 ≤ n)
    (hlo : n ^ 2 < x ^ 2) (hhi : x ^ 2 < (n + 1) ^ 2) : False := by
  have hlow : n < |x| := (sq_lt_sq₀ hn (abs_nonneg x)).mp (by simpa using hlo)
  have hhigh : |x| < n + 1 :=
    (sq_lt_sq₀ (abs_nonneg x) (by omega)).mp (by simpa using hhi)
  omega

def firstUnit (Q : ℕ) : Pell.Solution₁ ((Q : ℤ) * (Q + 1)) :=
  Pell.Solution₁.mk (2 * Q + 1) 2 (by ring)

theorem firstUnit_fundamental {Q : ℕ} (hQ : 0 < Q) :
    Pell.IsFundamental (firstUnit Q) := by
  apply fundamental_of_minimal_y_sq (firstUnit Q)
    (by change (1 : ℤ) < 2 * Q + 1; omega) (by norm_num [firstUnit])
  intro b hb
  change (4 : ℤ) ≤ b.y ^ 2
  by_contra h
  have hy0 := abs_pos.mpr (Pell.Solution₁.y_ne_zero_of_one_lt_x hb)
  have hylt := abs_lt_of_sq_lt_sq (by omega : b.y ^ 2 < (2 : ℤ) ^ 2)
    (by norm_num : (0 : ℤ) ≤ 2)
  have hy : |b.y| = 1 := by omega
  have hysq : b.y ^ 2 = 1 := by nlinarith [sq_abs b.y]
  have hprop := b.prop
  have hQZ : (0 : ℤ) < Q := by exact_mod_cast hQ
  rw [hysq] at hprop
  exact not_sq_between Q b.x (by positivity) (by nlinarith) (by nlinarith)

#print axioms fundamental_of_minimal_y_sq
#print axioms not_sq_between
#print axioms firstUnit_fundamental

end PellMinimum
