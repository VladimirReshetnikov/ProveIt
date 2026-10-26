import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

/-!
The definition and fundamental-unit theorem below are copied unchanged from
NativePellBootstrap at repository commit 9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9.
They are meant to be moved into a shared low-level module, not duplicated.
The following trace invariant and negative-norm proof are new.
-/

namespace PellTracePrototype

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


/-- Powers of the explicit unit have first coordinate congruent to one modulo twice Q. -/
theorem pow_x_mod (Q k : ℕ) : (2 * Q : ℤ) ∣ (firstUnit Q ^ k).x - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Pell.Solution₁.x_mul]
      change (2 * Q : ℤ) ∣ (firstUnit Q ^ k).x * (2 * Q + 1) +
        Q * (Q + 1) * ((firstUnit Q ^ k).y * 2) - 1
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (firstUnit Q ^ k).x + (Q + 1) * (firstUnit Q ^ k).y, ?_⟩
      linear_combination ht

/-- A norm-one solution in the positive quadrant inherits the first-coordinate invariant. -/
theorem positive_x_mod {Q : ℕ} (hQ : 0 < Q)
    (u : Pell.Solution₁ ((Q : ℤ) * (Q + 1)))
    (hx : 0 < u.x) (hy : 0 ≤ u.y) : (2 * Q : ℤ) ∣ u.x - 1 := by
  obtain ⟨k, rfl⟩ := (firstUnit_fundamental hQ).eq_pow_of_nonneg hx hy
  exact pow_x_mod Q k

/-- A norm-minus-one solution would square to a forbidden first-coordinate residue class. -/
theorem norm_ne_neg_one (n x y : ℤ) (hn : 2 ≤ n) :
    x ^ 2 - n * (n + 1) * y ^ 2 ≠ -1 := by
  lift n to ℕ using (by omega : 0 ≤ n)
  intro h
  have hp : (2 * x ^ 2 + 1) ^ 2 - (n : ℤ) * (n + 1) * |2 * x * y| ^ 2 = 1 := by
    rw [sq_abs]
    linear_combination 4 * x ^ 2 * h
  let u := Pell.Solution₁.mk (2 * x ^ 2 + 1) |2 * x * y| hp
  have hdvd := positive_x_mod (Q := n) (by omega) u
    (by change (0 : ℤ) < 2 * x ^ 2 + 1; positivity)
    (by change (0 : ℤ) ≤ |2 * x * y|; positivity)
  change (2 * n : ℤ) ∣ (2 * x ^ 2 + 1) - 1 at hdvd
  have hdvd2 : (2 * n : ℤ) ∣ 2 := by
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨((n : ℤ) + 1) * y ^ 2 - t, ?_⟩
    linear_combination 2 * h - ht
  have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) hdvd2
  omega

#print axioms norm_ne_neg_one

end PellTracePrototype
