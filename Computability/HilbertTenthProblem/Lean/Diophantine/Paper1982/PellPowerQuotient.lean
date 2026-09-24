import Diophantine.Paper1982.PellQuotient

/-!
# The positive Pell quotient for the power equation in Jones 1982, §5

For `2 ≤ B < A` and `2 ≤ L`, the congruence
`χ_A(L) ≡ B^L + (A−B)ψ_A(L) (mod 2AB−B²−1)` has a strictly positive quotient.
This supplies the positive witness `α` in (D3), once `Q = B^L` and
`C₁ = ψ_A(L)` have been established in the necessity construction.
-/

namespace Jones1982

open Pell Diophantine

/-- The exponential comparison used to control the positive Pell quotient. -/
theorem pow_lt_pred_mul_double_succ_pow_pred {B L : ℕ} (hB : 2 ≤ B) (hL : 2 ≤ L) :
    B ^ L < (B - 1) * (2 * B + 1) ^ (L - 1) := by
  induction L, hL using Nat.le_induction with
  | base =>
      norm_num only [pow_one]
      zify [show 1 ≤ B by omega]
      nlinarith
  | succ L hL ih =>
      have hpow : (2 * B + 1) ^ (L + 1 - 1) = (2 * B + 1) ^ (L - 1) * (2 * B + 1) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [pow_succ, hpow]
      calc B ^ L * B < ((B - 1) * (2 * B + 1) ^ (L - 1)) * B :=
          Nat.mul_lt_mul_of_pos_right ih (by omega)
        _ ≤ ((B - 1) * (2 * B + 1) ^ (L - 1)) * (2 * B + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (B - 1) * ((2 * B + 1) ^ (L - 1) * (2 * B + 1)) := by ring

/-- The lower Pell coordinate dominates the power term with the required factor. -/
theorem pow_lt_pred_mul_psi {A B L : ℕ} (hA : 1 < A)
    (hB : 2 ≤ B) (hBA : B < A) (hL : 2 ≤ L) :
    B ^ L < (B - 1) * ψ hA L := by
  have hψ : (2 * A - 1) ^ (L - 1) ≤ ψ hA L := by
    have := pow_le_ψ_succ hA (L - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ L)] at this
  calc B ^ L < (B - 1) * (2 * B + 1) ^ (L - 1) :=
      pow_lt_pred_mul_double_succ_pow_pred hB hL
    _ ≤ (B - 1) * (2 * A - 1) ^ (L - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ ≤ (B - 1) * ψ hA L := Nat.mul_le_mul_left _ hψ

/-- The numerator of the quotient in (D3) is strictly positive. -/
theorem pow_add_mul_psi_lt_chi {A B L : ℕ} (hA : 1 < A)
    (hB : 2 ≤ B) (hBA : B < A) (hL : 2 ≤ L) :
    B ^ L + (A - B) * ψ hA L < χ hA L := by
  have hpow := pow_lt_pred_mul_psi hA hB hBA hL
  have hχ := χ_gt hA L
  have hsplit : (A - 1) * ψ hA L = (A - B) * ψ hA L + (B - 1) * ψ hA L := by
    rw [show A - 1 = (A - B) + (B - 1) by omega]
    ring
  omega

/-- The positive natural-number quotient used for `α` in (D3). -/
theorem exists_positive_pell_power_quotient {A B L : ℕ} (hA : 1 < A)
    (hB : 2 ≤ B) (hBA : B < A) (hL : 2 ≤ L) :
    ∃ γ : ℕ, 0 < γ ∧
      χ hA L = B ^ L + (A - B) * ψ hA L + γ * (2 * A * B - B ^ 2 - 1) := by
  have hlt := pow_add_mul_psi_lt_chi hA hB hBA hL
  have hcong := χ_modEq_pow hA (p := B) (by omega) hBA.le L
  have hmod : 2 * A * B - B * B - 1 = 2 * A * B - B ^ 2 - 1 := by rw [sq]
  rw [hmod, mul_comm (ψ hA L) (A - B)] at hcong
  obtain ⟨γ, hγ⟩ := (Nat.modEq_iff_dvd' hlt.le).1 hcong.symm
  have hγpos : 0 < γ := by
    by_contra hn
    have : γ = 0 := by omega
    rw [this, mul_zero] at hγ
    omega
  refine ⟨γ, hγpos, ?_⟩
  rw [mul_comm γ]
  omega

/-- The exact integer equation for the positive quotient in (D3).
Both subtractions are ordinary integer subtraction. -/
theorem exists_positive_pell_power_quotient_int {A B L : ℕ} (hA : 1 < A)
    (hB : 2 ≤ B) (hBA : B < A) (hL : 2 ≤ L) :
    ∃ γ : ℕ, 0 < γ ∧
      (χ hA L : ℤ) = (B : ℤ) ^ L + ((A : ℤ) - B) * ψ hA L +
        γ * (2 * (A : ℤ) * B - (B : ℤ) ^ 2 - 1) := by
  obtain ⟨γ, hγ, h⟩ := exists_positive_pell_power_quotient hA hB hBA hL
  have hBsq : B ^ 2 < 2 * A * B := by
    have := Nat.mul_le_mul_right B hBA.le
    have : 0 < A * B := Nat.mul_pos (by omega) (by omega)
    nlinarith
  refine ⟨γ, hγ, ?_⟩
  have h' := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast [Nat.cast_sub hBA.le, Nat.cast_sub hBsq.le,
    Nat.cast_sub (by omega : 1 ≤ 2 * A * B - B ^ 2)] at h'
  exact h'

end Jones1982
