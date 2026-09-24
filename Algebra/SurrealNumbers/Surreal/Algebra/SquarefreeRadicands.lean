import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Sqrt
import Mathlib.Tactic

/-!
# Uniqueness of squarefree rational radicands

The elementary arithmetic prerequisite of `odg:def:lem:tailored`:
two squarefree natural radicands in the same rational square class coincide.
-/

namespace Surreal.SquarefreeRadicands

/-- A square product of squarefree naturals forces the factors to agree. -/
theorem eq_of_mul_isSquare {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (h : IsSquare (m * n)) : m = n := by
  obtain ⟨r, hr⟩ := h
  have hdiv : r * r ∣ m * n := hr.symm ▸ dvd_rfl
  have hrm : r ∣ m := hn.dvd_of_squarefree_of_mul_dvd_mul_left hdiv
  have hrn : r ∣ n := hm.dvd_of_squarefree_of_mul_dvd_mul_right hdiv
  have hmr : m ∣ r := (hm.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (by
    rw [pow_two, ← hr]
    exact dvd_mul_right _ _)
  have hnr : n ∣ r := (hn.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (by
    rw [pow_two, ← hr]
    exact dvd_mul_left _ _)
  exact (Nat.dvd_antisymm hmr hrm).trans (Nat.dvd_antisymm hrn hnr)

/-- Rational square factors cannot change a squarefree natural radicand. -/
theorem eq_of_rat_square_factor {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (r : ℚ) (h : (m : ℚ) = (n : ℚ) * r ^ 2) : m = n := by
  apply eq_of_mul_isSquare hm hn
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(n : ℚ) * r, ?_⟩
  push_cast
  rw [h]
  ring

/-- The only squarefree natural that is a rational square is one. -/
theorem eq_one_of_rat_isSquare {n : ℕ} (hn : Squarefree n) (h : IsSquare (n : ℚ)) : n = 1 := by
  obtain ⟨r, hr⟩ := h
  exact eq_of_rat_square_factor hn squarefree_one r (by simpa [pow_two] using hr)

end Surreal.SquarefreeRadicands
