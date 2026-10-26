import Std

/-!
Core-only exact rounding mechanism for the half-binomial ratio.
No real numbers, rational numbers, or binomial estimates are assumed here.
The production adapter must supply the exact numerator decomposition and
the two cross-multiplied Pell inequalities displayed in the theorem.
-/

namespace ResidualArithmetic

theorem rational_window_unique {k c a b : Nat}
    (haLow : k * a < c) (haHigh : c < k * (a + 1))
    (hbLow : k * b < c) (hbHigh : c < k * (b + 1)) : a = b := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro h
    have hba : b + 1 ≤ a := by omega
    have hm := Nat.mul_le_mul_left k hba
    omega
  · apply Nat.le_of_not_lt
    intro h
    have hab : a + 1 ≤ b := by omega
    have hm := Nat.mul_le_mul_left k hab
    omega

theorem half_quotient_window {D k c t s : Nat} (_hD : 0 < D) (hk : 0 < k)
    (hs : s < D)
    (hLow : k * (2 * t * D + s) < 2 * c * D)
    (hHigh : 2 * c * D < k * (2 * t * D + s + D)) :
    k * t < c ∧ c < k * (t + 1) := by
  constructor
  · apply Nat.lt_of_not_ge
    intro hc
    have hm := Nat.mul_le_mul_left (2 * D) hc
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] at hLow hm
    omega
  · apply Nat.lt_of_not_ge
    intro hc
    have hm := Nat.mul_le_mul_left (2 * D) hc
    have hs' := Nat.mul_lt_mul_of_pos_left hs hk
    have hdouble : D * (k * 2) = D * k + D * k := by
      simp only [Nat.mul_two, Nat.mul_add]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] at hHigh hm hs'
    omega

/-- The exact quotient identifies the source's interval index. -/
theorem half_quotient_rounding {A D k c t s Y : Nat}
    (hD : 0 < D) (hk : 0 < k) (hs : s < D)
    (hA : A = 2 * t * D + s)
    (hLow : k * A < 2 * c * D)
    (hHigh : 2 * c * D < k * (A + D))
    (hYLow : k * Y < c) (hYHigh : c < k * (Y + 1)) : Y = t := by
  rw [hA] at hLow hHigh
  have ht := half_quotient_window hD hk hs hLow hHigh
  exact rational_window_unique hYLow hYHigh ht.1 ht.2

#print axioms rational_window_unique
#print axioms half_quotient_window
#print axioms half_quotient_rounding

end ResidualArithmetic
