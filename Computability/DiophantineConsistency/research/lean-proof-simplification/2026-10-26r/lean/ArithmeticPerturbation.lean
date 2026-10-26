import Std

/-!
Integer form of a quantitative Pell ratio estimate. The perturbation bound,
power-sandwich majorant, and exact error-budget consequences are all checked
here. Instantiation with the production Pell growth estimates remains an
integration obligation. No ordered fields or real numbers are used.
-/

namespace ResidualArithmetic

/-- A denominator-cleared perturbation bound, proved without ordered fields. -/
theorem perturbed_power_le {H b r : Nat} (hbudget : 2 * r * b ≤ H) :
    H * (H + b) ^ r ≤ H ^ r * (H + 2 * r * b) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hprev : 2 * r * b ≤ H := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one] at hbudget
        omega
      have hstep : (H + 2 * r * b) * (H + b) ≤ H * (H + 2 * (r + 1) * b) := by
        have hm := Nat.mul_le_mul_right b hprev
        simp only [Nat.mul_two, Nat.mul_add, Nat.mul_one,
          Nat.mul_left_comm, Nat.mul_comm] at hm ⊢
        omega
      calc
        H * (H + b) ^ (r + 1) = (H * (H + b) ^ r) * (H + b) := by
          simp only [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ (H ^ r * (H + 2 * r * b)) * (H + b) :=
          Nat.mul_le_mul_right _ (ih hprev)
        _ = H ^ r * ((H + 2 * r * b) * (H + b)) := Nat.mul_assoc _ _ _
        _ ≤ H ^ r * (H * (H + 2 * (r + 1) * b)) := Nat.mul_le_mul_left _ hstep
        _ = H ^ (r + 1) * (H + 2 * (r + 1) * b) := by
          simp only [Nat.pow_succ, Nat.mul_assoc]

/-- The full scalar majorant from growth bounds and a one-step comparison. -/
theorem majorant_of_power_sandwich {H Z Q V W b r : Nat}
    (hH : 0 < H) (hkey : Z * H ≤ Q * (H + b))
    (hV : V ≤ Z ^ r) (hW : Q ^ r ≤ W) (hbudget : 2 * r * b ≤ H) :
    V * H ≤ W * (H + 2 * r * b) := by
  have hbound : (V * H) * H ^ r ≤ (W * (H + 2 * r * b)) * H ^ r := by
    calc
      (V * H) * H ^ r = (V * H ^ r) * H := by
        simp only [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ (Z ^ r * H ^ r) * H :=
        Nat.mul_le_mul_right H (Nat.mul_le_mul_right _ hV)
      _ = (Z * H) ^ r * H := by rw [Nat.mul_pow]
      _ ≤ (Q * (H + b)) ^ r * H :=
        Nat.mul_le_mul_right H (Nat.pow_le_pow_left hkey r)
      _ = Q ^ r * (H * (H + b) ^ r) := by
        simp only [Nat.mul_pow, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ Q ^ r * (H ^ r * (H + 2 * r * b)) :=
        Nat.mul_le_mul_left _ (perturbed_power_le hbudget)
      _ ≤ W * (H ^ r * (H + 2 * r * b)) := Nat.mul_le_mul_right _ hW
      _ = (W * (H + 2 * r * b)) * H ^ r := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos hH)

/-- `q*N*e < D*H` turns a relative majorant into error less than `1/q`. -/
theorem ratio_error_of_budget {c D H K N e q : Nat} (hK : 0 < K)
    (hmajor : c * D * H ≤ K * N * (H + e))
    (hbudget : q * N * e < D * H) :
    q * c * D < K * (q * N + D) := by
  have hm := Nat.mul_le_mul_left q hmajor
  have he := Nat.mul_lt_mul_of_pos_left hbudget hK
  have ht : (q * c * D) * H < (K * (q * N + D)) * H := by
    simp only [Nat.mul_add, Nat.mul_left_comm,
      Nat.mul_comm] at hm he ⊢
    omega
  exact Nat.lt_of_mul_lt_mul_right ht

/-- The native denominator is twice the undoubled Pell ordinate. -/
theorem doubled_ratio_upper_of_budget {c D H K N e k : Nat} (hK : 0 < K)
    (hmajor : c * D * H ≤ K * N * (H + e))
    (hbudget : N * e < D * H) (hk : k = 2 * K) :
    2 * c * D < k * (N + D) := by
  have h := ratio_error_of_budget (q := 1) hK hmajor
    (by simpa only [Nat.one_mul] using hbudget)
  simp only [Nat.one_mul] at h
  have h2 := Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2)
  simpa only [hk, Nat.mul_assoc] using h2

#print axioms perturbed_power_le
#print axioms majorant_of_power_sandwich
#print axioms ratio_error_of_budget
#print axioms doubled_ratio_upper_of_budget

end ResidualArithmetic
