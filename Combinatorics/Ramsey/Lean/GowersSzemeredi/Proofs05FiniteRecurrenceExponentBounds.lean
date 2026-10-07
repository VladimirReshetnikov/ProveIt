import GowersSzemeredi.Proofs05FiniteRecurrencePowers
import GowersSzemeredi.Proofs05DegreeBudgets

/-! Compare the explicit recurrence exponents with the factorial-exponential
constants used in the paper's polynomial localization induction. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

theorem finiteRecurrenceDivisor_bounds {k : Nat} (hk : 3 ≤ k) :
    k - 1 ≤ finiteRecurrenceDivisor k ∧ finiteRecurrenceDivisor k ≤ k ^ 2 := by
  have he : k - 1 + 1 = k := by omega
  unfold finiteRecurrenceDivisor
  constructor <;> nlinarith

theorem finiteRecurrenceCoefficientExponent_bound {k : Nat} (hk : 3 ≤ k) :
    finiteRecurrenceCoefficientExponent k ≤ 4 * k ^ 3 * 2 ^ finiteRecurrenceDivisor k := by
  let m := finiteRecurrenceDivisor k
  let V := 2 ^ m
  have hm := finiteRecurrenceDivisor_bounds hk
  have hW : weylDifferencingPower k ≤ V := Nat.pow_le_pow_right (by omega) hm.1
  have hV : 1 ≤ V := one_le_pow₀ (by omega)
  have hcube : 1 ≤ k ^ 3 := one_le_pow₀ (by omega)
  have hpoly : k ^ 2 + 3 * k + 12 ≤ 2 * k ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (k ^ 2) hk]
  have hmul : (k - 1) * m ≤ k ^ 3 := by
    have h := Nat.mul_le_mul (Nat.sub_le k 1) hm.2
    nlinarith only [h]
  calc
    _ = weylDifferencingPower k + (k ^ 2 + 3 * k + 12) + ((k - 1) * m) * V := by
      dsimp [finiteRecurrenceCoefficientExponent, m, V]
      ring
    _ ≤ V + (2 * k ^ 3) * V + k ^ 3 * V := by
      gcongr
      exact hpoly.trans (Nat.le_mul_of_pos_right _ (by omega))
    _ ≤ _ := by
      change _ ≤ 4 * k ^ 3 * V
      nlinarith only [Nat.mul_le_mul_right V hcube]

theorem finiteRecurrence_overhead_bound {k : Nat} (hk : 3 ≤ k) :
    finiteRecurrenceConstantExponent k + (k + 7) * finiteRecurrenceRadiusExponent k + 2 ≤
      32 * k ^ 5 * 2 ^ finiteRecurrenceDivisor k := by
  let m := finiteRecurrenceDivisor k
  let V := 2 ^ m
  have hm := (finiteRecurrenceDivisor_bounds hk).2
  have hW : weylDifferencingPower k ≤ V :=
    Nat.pow_le_pow_right (by omega) (finiteRecurrenceDivisor_bounds hk).1
  have hV : 1 ≤ V := one_le_pow₀ (by omega)
  have hc : finiteRecurrenceCoefficientExponent k ≤ 4 * k ^ 3 * V :=
    finiteRecurrenceCoefficientExponent_bound hk
  have hpoly : 35 + 4 * k ^ 3 + 2 * k ^ 2 + 4 * k ≤ 8 * k ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (k ^ 2) hk]
  have hinside : 4 + 3 * weylDifferencingPower k + finiteRecurrenceCoefficientExponent k +
      2 * m + (k + 7) * (weylDifferencingPower k + 3) ≤ 8 * k ^ 3 * V := by
    calc
      _ ≤ 4 * V + 3 * V + 4 * k ^ 3 * V + 2 * k ^ 2 * V + (k + 7) * (V + 3 * V) := by
        have hmV : m ≤ k ^ 2 * V := hm.trans (Nat.le_mul_of_pos_right _ (by omega))
        have h3 : 3 ≤ 3 * V := by omega
        have h4 : 4 ≤ 4 * V := by omega
        have hlast := Nat.mul_le_mul_left (k + 7) (Nat.add_le_add hW h3)
        nlinarith only [h4, hW, hc, hmV, hlast]
      _ = (35 + 4 * k ^ 3 + 2 * k ^ 2 + 4 * k) * V := by ring
      _ ≤ _ := Nat.mul_le_mul_right V hpoly
  have hmain : finiteRecurrenceConstantExponent k + (k + 7) * finiteRecurrenceRadiusExponent k ≤
      16 * k ^ 5 * V := by
    calc
      _ = 2 * m * (4 + 3 * weylDifferencingPower k + finiteRecurrenceCoefficientExponent k +
        2 * m + (k + 7) * (weylDifferencingPower k + 3)) := by
          dsimp [finiteRecurrenceConstantExponent, finiteRecurrenceRadiusExponent, m]
          ring
      _ ≤ 2 * k ^ 2 * (8 * k ^ 3 * V) := by gcongr
      _ = _ := by ring
  have hpos : 1 ≤ k ^ 5 * V := Nat.mul_pos (by positivity) (by positivity)
  change _ ≤ 32 * k ^ 5 * V
  nlinarith only [hmain, hpos]

end LeanProofs.GowersSzemeredi
