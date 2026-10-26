import Std

/-!
Core-only model of the positive Pell pair recurrence.  The recurrence is
exactly the one exposed by Mathlib's `Pell.xn_succ` and `Pell.yn_succ`.
This file does not import or replace the production Pell development.
-/

namespace ResidualArithmetic

def pellPair (A : Nat) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 =>
      let q := pellPair A n
      (q.1 * A + (A * A - 1) * q.2, q.1 + q.2 * A)

/-- An exact adapter for any implementation exposing the same recurrences. -/
theorem pellPair_eq_of_recurrences (A : Nat) (x y : Nat → Nat)
    (hx0 : x 0 = 1) (hy0 : y 0 = 0)
    (hxs : ∀ n, x (n + 1) = x n * A + (A * A - 1) * y n)
    (hys : ∀ n, y (n + 1) = x n + y n * A) (n : Nat) :
    pellPair A n = (x n, y n) := by
  induction n with
  | zero => simp only [pellPair, hx0, hy0]
  | succ n ih => simp only [pellPair, ih, hxs, hys]

theorem pellPair_mono_base {A B : Nat} (hAB : A ≤ B) (n : Nat) :
    (pellPair A n).1 ≤ (pellPair B n).1 ∧
      (pellPair A n).2 ≤ (pellPair B n).2 := by
  induction n with
  | zero => exact ⟨Nat.le_refl 1, Nat.le_refl 0⟩
  | succ n ih =>
      exact ⟨Nat.add_le_add (Nat.mul_le_mul ih.1 hAB)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul hAB hAB) 1) ih.2),
        Nat.add_le_add ih.1 (Nat.mul_le_mul ih.2 hAB)⟩

theorem pellPair_y_le_succ {A : Nat} (hA : 1 ≤ A) (n : Nat) :
    (pellPair A n).2 ≤ (pellPair A (n + 1)).2 := by
  change (pellPair A n).2 ≤ (pellPair A n).1 + (pellPair A n).2 * A
  have hm : (pellPair A n).2 ≤ (pellPair A n).2 * A := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (pellPair A n).2 hA
  omega

theorem pellPair_y_mono_index {A p n : Nat} (hA : 1 ≤ A) (hpn : p ≤ n) :
    (pellPair A p).2 ≤ (pellPair A n).2 := by
  induction n generalizing p with
  | zero =>
      have hp : p = 0 := by omega
      subst p
      exact Nat.le_refl _
  | succ n ih =>
      by_cases hp : p = n + 1
      · subst p
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (pellPair_y_le_succ hA n)

/-- Comparing actual sequence values eliminates exponential sandwich bounds. -/
theorem index_lt_of_gap {A B p n c k : Nat} (hAB : A ≤ B) (hB : 1 ≤ B)
    (hc : c = (pellPair A p).2) (hk : (pellPair B n).2 ≤ k)
    (hkc : k < c) : n < p := by
  apply Nat.lt_of_not_ge
  intro hpn
  have hbase := (pellPair_mono_base hAB p).2
  have hindex := pellPair_y_mono_index hB hpn
  omega

#print axioms pellPair_eq_of_recurrences
#print axioms pellPair_mono_base
#print axioms pellPair_y_mono_index
#print axioms index_lt_of_gap

end ResidualArithmetic
