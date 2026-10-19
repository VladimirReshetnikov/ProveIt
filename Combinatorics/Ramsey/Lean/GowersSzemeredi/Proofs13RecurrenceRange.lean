import GowersSzemeredi.Proofs13SingletonRecurrence
import Mathlib.Algebra.Polynomial.Degree.Monomial
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Fintype.EquivFin

/-! Precise coverage of the remaining Lemma 13.5 scales. The singleton
and polynomial branches overlap whenever there are at least 311 frequencies.

`lemma_13_5_failure_forces_intermediate_scale`,
`lemma_13_5_large_frequency_family` and `stage134_odd_of_polynomial_threshold`
are in `Proofs13RecurrenceRangeSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private theorem twice_square_tower_le (a : Nat) :
    2 * ((2 : Nat) ^ (2 ^ a)) ^ 2 ≤ 2 ^ (2 ^ (a + 2)) := by
  rw [← pow_mul, ← pow_succ']
  apply Nat.pow_le_pow_right (n := 2) (by norm_num)
  rw [pow_add]
  norm_num only [Nat.reducePow]
  have h : 1 ≤ (2 : Nat) ^ a := one_le_pow₀ (by norm_num)
  omega

theorem polynomial_threshold_twice_le_tower (d : Nat) :
    2 * polynomialPartitionThreshold d ≤ 2 ^ (2 ^ (40 * d ^ 3 + 2)) := by
  unfold polynomialPartitionThreshold weylThreshold
  exact twice_square_tower_le _

theorem simultaneous_partition_threshold_le_tower (k q b : Nat)
    (hK : polynomialPartitionConstant k ≤ 2 ^ b) :
    simultaneousPolynomialThreshold k q ≤ 2 ^ (2 ^ (40 * k ^ 3 + 2 + b * (q - 1))) := by
  calc
    simultaneousPolynomialThreshold k q =
      (2 * polynomialPartitionThreshold k) ^ (polynomialPartitionConstant k ^ (q - 1)) := rfl
    _ ≤ (2 ^ (2 ^ (40 * k ^ 3 + 2))) ^ (polynomialPartitionConstant k ^ (q - 1)) :=
      Nat.pow_le_pow_left (polynomial_threshold_twice_le_tower k) _
    _ ≤ (2 ^ (2 ^ (40 * k ^ 3 + 2))) ^ ((2 ^ b) ^ (q - 1)) :=
      Nat.pow_le_pow_right (n := 2 ^ (2 ^ (40 * k ^ 3 + 2)))
        (one_le_pow₀ (by norm_num : (1 : Nat) ≤ 2)) (Nat.pow_le_pow_left hK _)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]

end LeanProofs.GowersSzemeredi
