import GowersSzemeredi.Proofs05FiniteRecurrenceScale

/-! Integer power bounds for the explicit finite recurrence sample. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

def finiteRecurrenceCoefficientExponent (k : Nat) : Nat :=
  let m := finiteRecurrenceDivisor k
  weylDifferencingPower k + k ^ 2 + 3 * k + 12 + (k - 1) * m * 2 ^ m

def finiteRecurrenceConstantExponent (k : Nat) : Nat :=
  let m := finiteRecurrenceDivisor k
  2 * m * (4 + 3 * weylDifferencingPower k + finiteRecurrenceCoefficientExponent k + 2 * m)

def finiteRecurrenceRadiusExponent (k : Nat) : Nat :=
  2 * finiteRecurrenceDivisor k * (weylDifferencingPower k + 3)

theorem finiteWeylCoefficient_le_power (k : Nat) :
    finiteWeylCoefficient k (finiteRecurrenceDivisor k) ≤
      2 ^ finiteRecurrenceCoefficientExponent k := by
  let m := finiteRecurrenceDivisor k
  have hfac : Nat.factorial k ≤ 2 ^ (k ^ 2) := by
    calc
      _ ≤ k ^ k := Nat.factorial_le_pow k
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := k)).le k
      _ = _ := by rw [← pow_mul, pow_two]
  have hm : m ≤ 2 ^ m := (Nat.lt_two_pow_self (n := m)).le
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  unfold finiteWeylCoefficient
  calc
    _ ≤ 2 ^ (weylDifferencingPower k + 2 * k + 12) * 2 ^ (k ^ 2) *
        (2 ^ m) ^ ((k - 1) * 2 ^ m) * 2 ^ k := by gcongr
    _ = _ := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      dsimp [finiteRecurrenceCoefficientExponent, m]
      ring

theorem finiteRecurrenceSample_le_power (k R : Nat) :
    finiteRecurrenceSample k R ≤
      2 ^ finiteRecurrenceConstantExponent k * R ^ finiteRecurrenceRadiusExponent k := by
  let m := finiteRecurrenceDivisor k
  let W := weylDifferencingPower k
  let c := finiteRecurrenceCoefficientExponent k
  have hc := finiteWeylCoefficient_le_power k
  have hm : 2 * m + 1 ≤ 2 ^ (2 * m) := Nat.lt_two_pow_self
  have hbase : finiteRecurrenceBase k R ≤
      2 ^ (4 + 3 * W + c + 2 * m) * R ^ (W + 3) := by
    change 16 * 8 ^ W * finiteWeylCoefficient k m * (2 * m + 1) * R ^ (W + 3) ≤ _
    calc
      _ ≤ 16 * 8 ^ W * 2 ^ c * 2 ^ (2 * m) * R ^ (W + 3) := by gcongr
      _ = _ := by
        rw [show (16 : Nat) = 2 ^ 4 by norm_num, show (8 : Nat) = 2 ^ 3 by norm_num,
          ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  calc
    _ ≤ (2 ^ (4 + 3 * W + c + 2 * m) * R ^ (W + 3)) ^ (2 * m) :=
      Nat.pow_le_pow_left hbase _
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2 <;> dsimp [finiteRecurrenceConstantExponent, finiteRecurrenceRadiusExponent, m, W, c] <;> ring

end LeanProofs.GowersSzemeredi
