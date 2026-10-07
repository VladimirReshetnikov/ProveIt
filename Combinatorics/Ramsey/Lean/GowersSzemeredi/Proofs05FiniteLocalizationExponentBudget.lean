import GowersSzemeredi.Proofs05FiniteRecurrenceExponentBounds

/-! Split the next-degree localization exponent between the previous-degree
partition and the explicit recurrence overhead. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

theorem finiteRecurrence_overhead_quarter {k : Nat} (hk : 3 ≤ k) :
    4 * (finiteRecurrenceConstantExponent k + (k + 7) * finiteRecurrenceRadiusExponent k + 2) ≤
      polynomialPartitionConstant k := by
  by_cases hk5 : 5 ≤ k
  · have hpred : k - 1 + 1 = k := by omega
    have hkpow : k ≤ 2 ^ (k - 1) := by have := Nat.lt_two_pow_self (n := k - 1); omega
    have hcube : k ^ 3 ≤ 2 ^ (3 * (k - 1)) := by
      have h := Nat.pow_le_pow_left hkpow 3
      simpa only [← pow_mul, Nat.mul_comm] using h
    have he : 7 + 3 * (k - 1) + finiteRecurrenceDivisor k ≤ (k + 1) ^ 2 := by
      unfold finiteRecurrenceDivisor
      nlinarith
    calc
      _ ≤ 4 * (32 * k ^ 5 * 2 ^ finiteRecurrenceDivisor k) :=
        Nat.mul_le_mul_left 4 (finiteRecurrence_overhead_bound hk)
      _ = k ^ 2 * (2 ^ 7 * k ^ 3 * 2 ^ finiteRecurrenceDivisor k) := by ring
      _ ≤ k ^ 2 * (2 ^ 7 * 2 ^ (3 * (k - 1)) * 2 ^ finiteRecurrenceDivisor k) := by gcongr
      _ = k ^ 2 * 2 ^ (7 + 3 * (k - 1) + finiteRecurrenceDivisor k) := by rw [pow_add, pow_add]
      _ ≤ Nat.factorial k ^ 2 * 2 ^ ((k + 1) ^ 2) := Nat.mul_le_mul
        (Nat.pow_le_pow_left (Nat.self_le_factorial k) 2) (Nat.pow_le_pow_right (by omega) he)
      _ = _ := rfl
  · have he : k = 3 ∨ k = 4 := by omega
    rcases he with rfl | rfl <;>
      norm_num [finiteRecurrenceConstantExponent, finiteRecurrenceRadiusExponent,
        finiteRecurrenceCoefficientExponent, finiteRecurrenceDivisor,
        weylDifferencingPower, polynomialPartitionConstant]

theorem four_mul_add_one_le_two_pow {k : Nat} (hk : 5 ≤ k) : 4 * k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases h : 5 ≤ k
      · have hp := ih h
        rw [pow_succ]
        omega
      · have he : k = 4 := by omega
        subst k
        norm_num

theorem finiteRecurrence_induction_multiplier {k : Nat} (hk : 3 ≤ k) :
    4 * (k * finiteRecurrenceRadiusExponent k + 2) ≤ k ^ 2 * 2 ^ (2 * k + 1) := by
  by_cases hk5 : 5 ≤ k
  · let W := weylDifferencingPower k
    have hW : 4 ≤ W := by
      change 2 ^ 2 ≤ 2 ^ (k - 1)
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hm := (finiteRecurrenceDivisor_bounds hk).2
    have hB : finiteRecurrenceRadiusExponent k ≤ 4 * k ^ 2 * W := by
      unfold finiteRecurrenceRadiusExponent
      calc
        _ ≤ 2 * k ^ 2 * (2 * W) := by gcongr; omega
        _ = _ := by ring
    have hsmall : 2 ≤ k ^ 2 * W := by nlinarith
    have hpoly : k * finiteRecurrenceRadiusExponent k + 2 ≤ (4 * k + 1) * k ^ 2 * W := by
      nlinarith [Nat.mul_le_mul_left k hB]
    calc
      _ ≤ 4 * ((4 * k + 1) * k ^ 2 * W) := Nat.mul_le_mul_left 4 hpoly
      _ ≤ 4 * (2 ^ k * k ^ 2 * W) := by gcongr; exact four_mul_add_one_le_two_pow hk5
      _ = _ := by
        dsimp [W, weylDifferencingPower]
        have he : 2 * k + 1 = k + (k - 1) + 2 := by omega
        rw [he, pow_add, pow_add]
        ring
  · have he : k = 3 ∨ k = 4 := by omega
    rcases he with rfl | rfl <;>
      norm_num [finiteRecurrenceRadiusExponent, finiteRecurrenceDivisor, weylDifferencingPower]

theorem finiteLocalization_exponent_budget {k : Nat} (hk : 2 ≤ k) :
    finiteRecurrenceConstantExponent (k + 1) + (k + 1 + 7) * finiteRecurrenceRadiusExponent (k + 1) +
      ((k + 1) * finiteRecurrenceRadiusExponent (k + 1) + 2) * polynomialPartitionConstant k + 2 ≤
        polynomialPartitionConstant (k + 1) / 2 := by
  have hover := finiteRecurrence_overhead_quarter (by omega : 3 ≤ k + 1)
  have hmult := Nat.mul_le_mul_right (polynomialPartitionConstant k)
    (finiteRecurrence_induction_multiplier (by omega : 3 ≤ k + 1))
  have hK : polynomialPartitionConstant (k + 1) =
      ((k + 1) ^ 2 * 2 ^ (2 * (k + 1) + 1)) * polynomialPartitionConstant k := by
    rw [polynomialPartitionConstant_succ, pow_succ]
    ring
  rw [← hK] at hmult
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  nlinarith only [hover, hmult]

end LeanProofs.GowersSzemeredi
