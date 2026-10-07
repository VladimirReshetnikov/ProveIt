import GowersSzemeredi.Proofs05DegreeBudgets
import GowersSzemeredi.Proofs05Lemma9Scale

/-! The simultaneous partition threshold already pays for a factor-four
diameter reserve at every positive degree and every positive family size. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem polynomialPartitionConstant_double_le_exp {d : Nat} (hd : 1 ≤ d) :
    2 * polynomialPartitionConstant d ≤ 2 ^ (40 * d ^ 3) := by
  have hf : Nat.factorial d ≤ 2 ^ (d * d) := by
    calc
      Nat.factorial d ≤ d ^ d := Nat.factorial_le_pow d
      _ ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := d)).le d
      _ = 2 ^ (d * d) := (pow_mul _ _ _).symm
  have hd2 : d ≤ d ^ 2 := le_self_pow₀ hd (by norm_num)
  have hd3 : d ^ 2 ≤ d ^ 3 := pow_le_pow_right₀ hd (by norm_num)
  have hd31 : 1 ≤ d ^ 3 := one_le_pow₀ hd
  calc
    2 * polynomialPartitionConstant d ≤ 2 * ((2 ^ (d * d)) ^ 2 * 2 ^ ((d + 1) ^ 2)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hf 2))
    _ = 2 ^ (2 * d ^ 2 + (d + 1) ^ 2 + 1) := by
      rw [← pow_mul, ← pow_add, ← pow_succ']
      congr 1
      ring
    _ ≤ 2 ^ (40 * d ^ 3) := Nat.pow_le_pow_right (n := 2) (by norm_num) (by nlinarith)

theorem polynomialPartitionThreshold_sixteen_pow_of_bound (d : Nat)
    (h : 2 * polynomialPartitionConstant d ≤ 2 ^ (40 * d ^ 3)) :
    16 ^ polynomialPartitionConstant d ≤ polynomialPartitionThreshold d := by
  unfold polynomialPartitionThreshold weylThreshold
  calc
    16 ^ polynomialPartitionConstant d = (2 : Nat) ^ (4 * polynomialPartitionConstant d) := by
      rw [show (16 : Nat) = 2 ^ 4 by norm_num, ← pow_mul]
    _ ≤ 2 ^ (2 ^ (40 * d ^ 3) * 2) := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
    _ = (2 ^ 2 ^ (40 * d ^ 3)) ^ 2 := pow_mul _ _ _

theorem polynomialPartitionThreshold_sixteen_pow {d : Nat} (hd : 1 ≤ d) :
    16 ^ polynomialPartitionConstant d ≤ polynomialPartitionThreshold d :=
  polynomialPartitionThreshold_sixteen_pow_of_bound d (polynomialPartitionConstant_double_le_exp hd)

theorem simultaneous_partition_final_root {k q r : Nat} (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hthreshold : simultaneousPolynomialThreshold k q < r) :
    16 ≤ (r : Real) ^ ((polynomialPartitionConstant k : Real) ^ q)⁻¹ := by
  let K := polynomialPartitionConstant k
  let T := polynomialPartitionThreshold k
  have hK : 0 < K := by dsimp [K, polynomialPartitionConstant]; positivity
  have hbase : 16 ^ K ≤ 2 * T := (polynomialPartitionThreshold_sixteen_pow hk).trans
    (Nat.le_mul_of_pos_left _ (by norm_num))
  have hpow : (16 : Nat) ^ (K ^ q) ≤ r := by
    calc
      _ = (16 ^ K) ^ (K ^ (q - 1)) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega
      _ ≤ (2 * T) ^ (K ^ (q - 1)) := Nat.pow_le_pow_left (n := 16 ^ K) (m := 2 * T) hbase _
      _ ≤ r := hthreshold.le
  have hr : (0 : Real) ≤ r := Nat.cast_nonneg r
  have hexp : 0 < ((K ^ q : Nat) : Real) := by positivity
  have hroot : (16 : Real) ≤ (r : Real) ^ (((K ^ q : Nat) : Real)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hr hexp).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hpow
  simpa only [Nat.cast_pow, K] using hroot


end LeanProofs.GowersSzemeredi
