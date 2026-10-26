import Mathlib.NumberTheory.PellMatiyasevic

namespace NewArithmetic
open Pell

/-- A fixed finite anchor replaces variable-exponent growth estimates. -/
theorem large_of_six_le {A c p : ℕ} (hA : 1 < A) (hp : 6 ≤ p)
    (hcp : c = yn hA p) : A * (A ^ 2 - 1) ^ 2 < c := by
  have hlt : (A ^ 2 - 1) ^ 2 < (A ^ 2) ^ 2 :=
    Nat.pow_lt_pow_left (by have := Nat.one_le_pow 2 A (by omega); omega) two_ne_zero
  calc
    A * (A ^ 2 - 1) ^ 2 < A * (A ^ 2) ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hlt (by omega)
    _ = A ^ 5 := by simp [pow_succ, mul_assoc]
    _ ≤ xn hA 5 := xn_ge_a_pow hA 5
    _ ≤ yn hA 6 := Nat.le_add_right _ _
    _ ≤ c := by rw [hcp]; exact (strictMono_y hA).monotone hp

#print axioms large_of_six_le
end NewArithmetic
