import DiophantineConsistency.NativeLocalCoefficients54

/-! # Literal positive bit-coefficient recipes for the compact54 local clause -/

namespace DiophantineConsistency.NativeClauseBits54

open NativeClause54 NativeLocalCoefficients54
open scoped BigOperators

def binaryValue {n : ℕ} (x : Fin n → ℕ) : ℕ := ∑ j, x j * 2 ^ j.val

def rightBitCoefficient (j : Fin 8) : ℕ :=
  2 ^ (9+j.val) + 2 ^ 29 * (2 ^ (j.val+1) + 2 ^ (33+j.val))

def leftBitCoefficient (j : Fin 8) : ℕ :=
  2 ^ (18+j.val) + 2 ^ 29 * (2 ^ (22+j.val) + 2 ^ (33+j.val))

def commonBitCoefficient : ℕ := 2 ^ 27 + 2 ^ 29 * (2 ^ 11 + 2 ^ 32)
def anchorCoefficient : ℕ := 2 ^ 71

def copyBitCoefficient (j : Fin 42) : ℕ := 2 ^ (29+j.val) + if j = 0 then 2 ^ 71 else 0

theorem rightBitCoefficient_eq (j : Fin 8) :
    rightBitCoefficient j = 2 ^ j.val * (2 ^ 9 + 2 ^ 29 * (2 + 2 ^ 33)) := by
  unfold rightBitCoefficient
  simp only [pow_add]
  ring

theorem leftBitCoefficient_eq (j : Fin 8) :
    leftBitCoefficient j = 2 ^ j.val * (2 ^ 18 + 2 ^ 29 * (2 ^ 22 + 2 ^ 33)) := by
  unfold leftBitCoefficient
  simp only [pow_add]
  ring

/-- The bit recipes give the aggregate auxiliary word for arbitrary
nonnegative bit coefficients; no binary-value bound is used in the identity. -/
theorem auxiliaryWord_eq_bit_sum (r l : Fin 8 → ℕ) (u : ℕ) :
    auxiliaryWord (binaryValue r) (binaryValue l) u =
      (∑ j, r j * rightBitCoefficient j) + (∑ j, l j * leftBitCoefficient j) +
        u * commonBitCoefficient := by
  have hR : (∑ j, r j * rightBitCoefficient j) =
      binaryValue r * (2 ^ 9 + 2 ^ 29 * (2 + 2 ^ 33)) := by
    simp_rw [rightBitCoefficient_eq,← mul_assoc]
    rw [← Finset.sum_mul]
    rfl
  have hL : (∑ j, l j * leftBitCoefficient j) =
      binaryValue l * (2 ^ 18 + 2 ^ 29 * (2 ^ 22 + 2 ^ 33)) := by
    simp_rw [leftBitCoefficient_eq,← mul_assoc]
    rw [← Finset.sum_mul]
    rfl
  rw [hR,hL]
  unfold auxiliaryWord auxiliary commonBitCoefficient
  norm_num
  ring

theorem binaryValue_shift {n : ℕ} (x : Fin n → ℕ) (m : ℕ) :
    (∑ j, x j * 2 ^ (m+j.val)) = 2 ^ m * binaryValue x := by
  unfold binaryValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- The west parity bit is counted once in Z and once in the shared
anchor field, exactly as the actual coefficient at native position539. -/
theorem copiedWord_eq_bit_sum (z : Fin 42 → ℕ) (A1 A2 : ℕ) :
    copiedWord (binaryValue z) (z 0) A1 A2 =
      (∑ j, z j * copyBitCoefficient j) + A1 * anchorCoefficient + A2 * anchorCoefficient := by
  have hs : (∑ j, z j * copyBitCoefficient j) = 2 ^ 29 * binaryValue z + z 0 * 2 ^ 71 := by
    unfold copyBitCoefficient
    simp_rw [mul_add,mul_ite,mul_zero]
    rw [Finset.sum_add_distrib,binaryValue_shift]
    simp
  rw [hs]
  unfold copiedWord anchorCoefficient labelBase
  norm_num
  ring

end DiophantineConsistency.NativeClauseBits54
