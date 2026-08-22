import ExponentialIdentities.TwoBaseIntegerExponent.GeometricVandermondeSmith

/-!
# Finite geometric Newton interpolation

This file formalizes the exact finite algebraic core of report 19.  It is deliberately
separate from any convergence or approximation claim: the identities hold over `ℤ` for
arbitrary integer parameters.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators
open Finset

/-- The numerator coefficient in geometric Newton interpolation. -/
def qNewtonInterpolationCoeff (q r : ℤ) (k : ℕ) : ℤ :=
  ∏ i ∈ range k, (r - q ^ i)

@[simp] theorem qNewtonInterpolationCoeff_zero (q r : ℤ) :
    qNewtonInterpolationCoeff q r 0 = 1 := by
  simp [qNewtonInterpolationCoeff]

theorem qNewtonInterpolationCoeff_succ (q r : ℤ) (k : ℕ) :
    qNewtonInterpolationCoeff q r (k + 1) =
      qNewtonInterpolationCoeff q r k * (r - q ^ k) := by
  simp [qNewtonInterpolationCoeff, prod_range_succ]

theorem qNewtonInterpolationCoeff_add_qpow (q r : ℤ) (k : ℕ) :
    qNewtonInterpolationCoeff q r (k + 1) +
        q ^ k * qNewtonInterpolationCoeff q r k =
      r * qNewtonInterpolationCoeff q r k := by
  rw [qNewtonInterpolationCoeff_succ]
  ring

/-- The finite q-Newton expansion of the power data `q^n ↦ r^n`. -/
def qNewtonExpansion (q r : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), qPascal q n k * qNewtonInterpolationCoeff q r k

@[simp] theorem qNewtonExpansion_zero (q r : ℤ) :
    qNewtonExpansion q r 0 = 1 := by
  simp [qNewtonExpansion]

theorem qNewtonExpansion_succ (q r : ℤ) (n : ℕ) :
    qNewtonExpansion q r (n + 1) = r * qNewtonExpansion q r n := by
  have htail :
      (∑ k ∈ range (n + 1),
          q ^ (k + 1) * qPascal q n (k + 1) *
            qNewtonInterpolationCoeff q r (k + 1)) =
        ∑ k ∈ range n,
          q ^ (k + 1) * qPascal q n (k + 1) *
            qNewtonInterpolationCoeff q r (k + 1) := by
    rw [sum_range_succ]
    simp [qPascal_eq_zero_of_lt q (Nat.lt_succ_self n)]
  have hhead :
      (∑ k ∈ range (n + 1),
          q ^ k * qPascal q n k * qNewtonInterpolationCoeff q r k) =
        1 + ∑ k ∈ range n,
          q ^ (k + 1) * qPascal q n (k + 1) *
            qNewtonInterpolationCoeff q r (k + 1) := by
    rw [sum_range_succ']
    simp
    ring
  have hshift :
      1 + (∑ k ∈ range (n + 1),
          q ^ (k + 1) * qPascal q n (k + 1) *
            qNewtonInterpolationCoeff q r (k + 1)) =
        ∑ k ∈ range (n + 1),
          q ^ k * qPascal q n k * qNewtonInterpolationCoeff q r k := by
    calc
      1 + (∑ k ∈ range (n + 1),
          q ^ (k + 1) * qPascal q n (k + 1) *
            qNewtonInterpolationCoeff q r (k + 1)) =
          1 + ∑ k ∈ range n,
            q ^ (k + 1) * qPascal q n (k + 1) *
              qNewtonInterpolationCoeff q r (k + 1) := by rw [htail]
      _ = ∑ k ∈ range (n + 1),
          q ^ k * qPascal q n k * qNewtonInterpolationCoeff q r k := hhead.symm
  unfold qNewtonExpansion
  rw [sum_range_succ']
  simp only [qPascal_zero, qNewtonInterpolationCoeff_zero, mul_one,
    qPascal_succ_succ, add_mul, sum_add_distrib]
  calc
    ((∑ k ∈ range (n + 1),
        qPascal q n k * qNewtonInterpolationCoeff q r (k + 1)) +
      ∑ k ∈ range (n + 1),
        q ^ (k + 1) * qPascal q n (k + 1) *
          qNewtonInterpolationCoeff q r (k + 1)) + 1 =
        (∑ k ∈ range (n + 1),
            qPascal q n k * qNewtonInterpolationCoeff q r (k + 1)) +
          (1 + ∑ k ∈ range (n + 1),
            q ^ (k + 1) * qPascal q n (k + 1) *
              qNewtonInterpolationCoeff q r (k + 1)) := by ring
    _ =
        (∑ k ∈ range (n + 1),
            qPascal q n k * qNewtonInterpolationCoeff q r (k + 1)) +
          ∑ k ∈ range (n + 1),
            q ^ k * qPascal q n k * qNewtonInterpolationCoeff q r k := by
      rw [hshift]
    _ = ∑ k ∈ range (n + 1),
          r * (qPascal q n k * qNewtonInterpolationCoeff q r k) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [qNewtonInterpolationCoeff_succ]
      ring
    _ = r * ∑ k ∈ range (n + 1),
          qPascal q n k * qNewtonInterpolationCoeff q r k := by
      rw [mul_sum]

/-- Exact geometric Newton expansion (the finite q-binomial identity in report 19). -/
theorem qNewtonExpansion_eq_pow (q r : ℤ) (n : ℕ) :
    qNewtonExpansion q r n = r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qNewtonExpansion_succ, ih, pow_succ']

/-- Value at the `n`th geometric node of the degree-`d` q-Newton truncation. -/
def qNewtonTruncValue (q r : ℤ) (d n : ℕ) : ℤ :=
  ∑ k ∈ range (d + 1), qPascal q n k * qNewtonInterpolationCoeff q r k

/-- Up to its truncation degree, the finite geometric Newton expansion interpolates
the prescribed power data exactly. -/
theorem qNewtonTruncValue_eq_pow_of_le (q r : ℤ) {d n : ℕ} (hnd : n ≤ d) :
    qNewtonTruncValue q r d n = r ^ n := by
  induction d generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnd
      subst n
      simp [qNewtonTruncValue]
  | succ d ih =>
      rcases hnd.eq_or_lt with rfl | hlt
      · exact qNewtonExpansion_eq_pow q r (d + 1)
      · rw [qNewtonTruncValue, sum_range_succ]
        rw [qPascal_eq_zero_of_lt q hlt, zero_mul, add_zero]
        exact ih (by omega)

/-- Above the truncation degree, the residual is exactly the omitted q-Newton tail. -/
theorem qNewtonTruncValue_remainder (q r : ℤ) {d n : ℕ} (hdn : d ≤ n) :
    r ^ n - qNewtonTruncValue q r d n =
      ∑ k ∈ Ico (d + 1) (n + 1),
        qPascal q n k * qNewtonInterpolationCoeff q r k := by
  rw [← qNewtonExpansion_eq_pow q r n]
  unfold qNewtonExpansion qNewtonTruncValue
  exact (sum_Ico_eq_sub _ (Nat.succ_le_succ hdn)).symm

/-- The first omitted geometric-node residual is exactly the next Newton numerator. -/
theorem qNewtonTruncValue_first_omitted (q r : ℤ) (d : ℕ) :
    r ^ (d + 1) - qNewtonTruncValue q r d (d + 1) =
      qNewtonInterpolationCoeff q r (d + 1) := by
  rw [← qNewtonExpansion_eq_pow q r (d + 1)]
  unfold qNewtonExpansion qNewtonTruncValue
  rw [sum_range_succ]
  rw [qPascal_self]
  ring

end LeanProofs.TwoBaseIntegerExponent
