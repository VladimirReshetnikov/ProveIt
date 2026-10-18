import GowersSzemeredi.Proofs05DegreeScale

/-! # Integer threshold budgets for polynomial degree induction -/

set_option autoImplicit false

namespace LeanProofs.GowersSzemeredi

/-- Exact growth of the polynomial partition constant. -/
theorem polynomialPartitionConstant_succ (k : Nat) :
    polynomialPartitionConstant (k + 1) =
      2 * ((k + 1) ^ 2 * 2 ^ (2 * (k + 1))) * polynomialPartitionConstant k := by
  unfold polynomialPartitionConstant
  rw [Nat.factorial_succ, mul_pow]
  have hexp : (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + 2 * (k + 1) + 1 := by ring
  rw [hexp, pow_add, pow_add]
  ring

/-- The polynomial partition constants fit inside a single exponential. -/
theorem polynomialPartitionConstant_le_exp {d : Nat} (hd : 1 ≤ d) :
    polynomialPartitionConstant d ≤ 2 ^ (40 * d ^ 3) := by
  have hf : Nat.factorial d ≤ 2 ^ (d * d) := by
    calc
      Nat.factorial d ≤ d ^ d := Nat.factorial_le_pow d
      _ ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := d)).le d
      _ = 2 ^ (d * d) := (pow_mul _ _ _).symm
  calc
    polynomialPartitionConstant d ≤ (2 ^ (d * d)) ^ 2 * 2 ^ ((d + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hf 2)
    _ = 2 ^ (2 * d ^ 2 + (d + 1) ^ 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ (40 * d ^ 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith [sq_nonneg (d - 1 : Int)]

/-- The next threshold dominates the fourth-power requirement of rounding. -/
theorem polynomialPartitionThreshold_four_pow {d : Nat} (hd : 1 ≤ d) :
    4 ^ polynomialPartitionConstant d ≤ polynomialPartitionThreshold d := by
  have hK := polynomialPartitionConstant_le_exp hd
  unfold polynomialPartitionThreshold weylThreshold
  calc
    4 ^ polynomialPartitionConstant d = 2 ^ (2 * polynomialPartitionConstant d) := by
      rw [pow_mul]; norm_num
    _ ≤ 2 ^ (2 * 2 ^ (40 * d ^ 3)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ 2 ^ (40 * d ^ 3)) ^ 2 := by rw [← pow_mul]; congr 1; omega

/-- The next threshold leaves room for both possible rounded child lengths. -/
theorem polynomialPartitionThreshold_degree_budget {k : Nat} (hk : 1 ≤ k) :
    (2 * (polynomialPartitionThreshold k + 1)) ^ ((k + 1) ^ 2 * 2 ^ (2 * (k + 1))) ≤
      polynomialPartitionThreshold (k + 1) := by
  -- `T (k + 1) = (T k ^ 2) ^ 2 ^ (120 k ^ 2 + 120 k + 39)` and `2 (T k + 1) ≤ T k ^ 2`
  have hT : 4 ≤ polynomialPartitionThreshold k := by
    have := Nat.one_lt_two_pow (n := 2 ^ (40 * k ^ 3)) (by positivity)
    unfold polynomialPartitionThreshold weylThreshold; nlinarith
  have hE : (k + 1) ^ 2 * 2 ^ (2 * (k + 1)) ≤ 2 ^ (120 * k ^ 2 + 120 * k + 39) :=
    calc (k + 1) ^ 2 * 2 ^ (2 * (k + 1)) ≤ 2 ^ (2 * (k + 1)) * 2 ^ (2 * (k + 1)) := by
          gcongr ?_ * _; rw [pow_mul']; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc _ ≤ (polynomialPartitionThreshold k ^ 2) ^ 2 ^ (120 * k ^ 2 + 120 * k + 39) :=
        (Nat.pow_le_pow_left (by nlinarith) _).trans
          (Nat.pow_le_pow_right (pow_pos (by omega) _) hE)
    _ = polynomialPartitionThreshold (k + 1) := by
        simp only [polynomialPartitionThreshold, weylThreshold, ← pow_mul]
        exact congrArg (fun n : Nat => 2 ^ n) (by ring)

/-- Constant growth pays for the fourth-power rounding loss and the leading term. -/
theorem polynomialPartitionConstant_degree_budgets {k : Nat} (hk : 1 ≤ k) :
    8 * polynomialPartitionConstant k ≤ polynomialPartitionConstant (k + 1) ∧
    ((2 * polynomialPartitionConstant k * (k + 1) + 4 : Nat) : Real) ≤
      (polynomialPartitionConstant (k + 1) : Real) *
        (((k + 1 : Nat) : Real) * (2 : Real) ^ (k + 1 + 1))⁻¹ := by
  have hK : 0 < polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant; positivity
  rw [polynomialPartitionConstant_succ]
  generalize polynomialPartitionConstant k = K at hK ⊢
  refine ⟨Nat.mul_le_mul_right _ ?_, ?_⟩
  · linarith [Nat.mul_le_mul (Nat.pow_le_pow_left (show 2 ≤ k + 1 by omega) 2)
      (Nat.one_le_two_pow (n := 2 * (k + 1)))]
  · -- the right side is `K (k + 1) 2 ^ (k + 1)`
    have h : 2 * K * (k + 1) + 4 ≤ K * (k + 1) * 2 ^ (k + 1) := by
      nlinarith [Nat.mul_le_mul_left (K * (k + 1))
        (Nat.pow_le_pow_right two_pos (show 2 ≤ k + 1 by omega))]
    refine (Nat.cast_le.mpr h).trans_eq ?_
    push_cast; field_simp; ring

end LeanProofs.GowersSzemeredi
