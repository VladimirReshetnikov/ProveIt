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

private theorem partitionConstant_pos (k : Nat) : 1 ≤ polynomialPartitionConstant k := by
  unfold polynomialPartitionConstant
  have := Nat.factorial_pos k
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

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
  let d := k + 1
  let a := 2 ^ (40 * k ^ 3 + 1)
  have ha : 2 ≤ a := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ 40 * k ^ 3 + 1 by omega)
  have hT : polynomialPartitionThreshold k = 2 ^ a := by
    unfold polynomialPartitionThreshold weylThreshold a
    rw [← pow_mul]
    congr 1
  have hT1 : 1 ≤ polynomialPartitionThreshold k := by rw [hT]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hbase : 2 * (polynomialPartitionThreshold k + 1) ≤ 2 ^ (a + 2) := by
    rw [pow_add, ← hT]
    norm_num
    omega
  have hE : d ^ 2 * 2 ^ (2 * d) ≤ 2 ^ (4 * d) := by
    calc
      d ^ 2 * 2 ^ (2 * d) ≤ (2 ^ d) ^ 2 * 2 ^ (2 * d) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := d)).le 2)
      _ = 2 ^ (4 * d) := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have ha2 : a + 2 ≤ 2 ^ (40 * k ^ 3 + 2) := by
    have he : 40 * k ^ 3 + 2 = (40 * k ^ 3 + 1) + 1 := by omega
    rw [he, pow_succ]
    change a + 2 ≤ a * 2
    omega
  have hexp : (a + 2) * (d ^ 2 * 2 ^ (2 * d)) ≤ 2 ^ (40 * d ^ 3 + 1) := by
    calc
      (a + 2) * (d ^ 2 * 2 ^ (2 * d)) ≤ 2 ^ (40 * k ^ 3 + 2) * 2 ^ (4 * d) :=
        Nat.mul_le_mul ha2 hE
      _ = 2 ^ (40 * k ^ 3 + 2 + 4 * d) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (40 * d ^ 3 + 1) := by
        apply Nat.pow_le_pow_right (by norm_num)
        dsimp [d]
        nlinarith
  calc
    (2 * (polynomialPartitionThreshold k + 1)) ^ (d ^ 2 * 2 ^ (2 * d)) ≤
        (2 ^ (a + 2)) ^ (d ^ 2 * 2 ^ (2 * d)) := Nat.pow_le_pow_left hbase _
    _ ≤ 2 ^ 2 ^ (40 * d ^ 3 + 1) := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) hexp
    _ = polynomialPartitionThreshold (k + 1) := by
      unfold polynomialPartitionThreshold weylThreshold
      rw [← pow_mul, pow_succ]

/-- Constant growth pays for the fourth-power rounding loss and the leading term. -/
theorem polynomialPartitionConstant_degree_budgets {k : Nat} (hk : 1 ≤ k) :
    8 * polynomialPartitionConstant k ≤ polynomialPartitionConstant (k + 1) ∧
    ((2 * polynomialPartitionConstant k * (k + 1) + 4 : Nat) : Real) ≤
      (polynomialPartitionConstant (k + 1) : Real) *
        (((k + 1 : Nat) : Real) * (2 : Real) ^ (k + 1 + 1))⁻¹ := by
  let K := polynomialPartitionConstant k
  let d := k + 1
  have hK : 1 ≤ K := partitionConstant_pos k
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hp : 4 ≤ 2 ^ d := by
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) hd
  have hD : polynomialPartitionConstant (k + 1) = 2 * (d ^ 2 * 2 ^ (2 * d)) * K :=
    polynomialPartitionConstant_succ k
  constructor
  · rw [hD]
    change 8 * K ≤ 2 * (d ^ 2 * 2 ^ (2 * d)) * K
    have hpow : 1 ≤ 2 ^ (2 * d) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hE : 4 ≤ d ^ 2 * 2 ^ (2 * d) := by nlinarith
    nlinarith
  · have hdR : (d : Real) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have heq : (polynomialPartitionConstant (k + 1) : Real) *
        ((d : Real) * (2 : Real) ^ (d + 1))⁻¹ = (K : Real) * d * 2 ^ d := by
      rw [hD]
      push_cast
      rw [show 2 * d = d + d by omega, pow_add, pow_succ]
      field_simp
      ring
    change ((2 * K * d + 4 : Nat) : Real) ≤ _
    rw [heq]
    have hnat : 2 * K * d + 4 ≤ K * d * 2 ^ d := by
      have hKd : 2 ≤ K * d := by nlinarith
      nlinarith [Nat.mul_le_mul_left (K * d) hp]
    exact_mod_cast hnat

end LeanProofs.GowersSzemeredi
