import DiophantineConsistency.ConsecutivePellUnit

/-!
# Negative Pell norms for two consecutive factors

Square a hypothetical negative-norm solution, classify the positive norm-one
solution using the existing fundamental unit, and contradict its first coordinate modulo 2n.
-/

namespace DiophantineConsistency.ConsecutivePell

/-- Powers of the explicit unit have first coordinate congruent to one modulo twice Q. -/
theorem pow_x_mod (Q k : ℕ) : (2 * Q : ℤ) ∣ (NativePellBootstrap.firstUnit Q ^ k).x - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Pell.Solution₁.x_mul]
      change (2 * Q : ℤ) ∣ (NativePellBootstrap.firstUnit Q ^ k).x * (2 * Q + 1) +
        Q * (Q + 1) * ((NativePellBootstrap.firstUnit Q ^ k).y * 2) - 1
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (NativePellBootstrap.firstUnit Q ^ k).x + (Q + 1) * (NativePellBootstrap.firstUnit Q ^ k).y, ?_⟩
      linear_combination ht

/-- A norm-one solution in the positive quadrant inherits the first-coordinate invariant. -/
theorem positive_x_mod {Q : ℕ} (hQ : 0 < Q)
    (u : Pell.Solution₁ ((Q : ℤ) * (Q + 1)))
    (hx : 0 < u.x) (hy : 0 ≤ u.y) : (2 * Q : ℤ) ∣ u.x - 1 := by
  obtain ⟨k, rfl⟩ := (NativePellBootstrap.firstUnit_fundamental hQ).eq_pow_of_nonneg hx hy
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

end DiophantineConsistency.ConsecutivePell
