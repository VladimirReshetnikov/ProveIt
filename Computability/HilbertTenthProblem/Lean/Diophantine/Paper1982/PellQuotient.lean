import Diophantine.Common.Pell
import Mathlib.Tactic

/-!
# The positive Pell-congruence quotient in Jones 1982, Theorem 3

For `A ≥ 3` and `k ≥ 2`, the congruence
`χ_A(k) ≡ 2^k + (A−2)ψ_A(k) (mod 4A−5)` has a strictly positive quotient.
This supplies the positive witness `γ` in the printed Theorem 3, where
`k = 2r+1 ≥ 17`. The stronger lower threshold `k ≥ 2` also covers the first
nonzero quotient, at which `γ = 1`.
-/

namespace Jones1982

open Pell Diophantine

/-- The elementary exponential comparison behind the strict Pell bound. -/
theorem two_pow_lt_five_pow_pred {k : ℕ} (hk : 2 ≤ k) :
    2 ^ k < 5 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have he : 5 ^ (k + 1 - 1) = 5 ^ (k - 1) * 5 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he, pow_succ]
    nlinarith [Nat.zero_le (5 ^ (k - 1))]

/-- `ψ_A(k)` strictly exceeds `2^k` for `A ≥ 3` and `k ≥ 2`. -/
theorem two_pow_lt_psi {A k : ℕ} (hA : 1 < A) (hA3 : 3 ≤ A) (hk : 2 ≤ k) :
    2 ^ k < ψ hA k := by
  have hψ : (2 * A - 1) ^ (k - 1) ≤ ψ hA k := by
    have := pow_le_ψ_succ hA (k - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at this
  calc 2 ^ k < 5 ^ (k - 1) := two_pow_lt_five_pow_pred hk
    _ ≤ (2 * A - 1) ^ (k - 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ ψ hA k := hψ

/-- The numerator of Theorem 3's congruence quotient is strictly positive. -/
theorem two_pow_add_mul_psi_lt_chi {A k : ℕ}
    (hA : 1 < A) (hA3 : 3 ≤ A) (hk : 2 ≤ k) :
    2 ^ k + (A - 2) * ψ hA k < χ hA k := by
  have hpow := two_pow_lt_psi hA hA3 hk
  have hχ := χ_gt hA k
  have hsplit : (A - 1) * ψ hA k = (A - 2) * ψ hA k + ψ hA k := by
    rw [show A - 1 = (A - 2) + 1 by omega]
    ring
  omega

/-- The positive natural-number quotient used for `γ` in Theorem 3. -/
theorem exists_positive_pell_quotient {A k : ℕ}
    (hA : 1 < A) (hA3 : 3 ≤ A) (hk : 2 ≤ k) :
    ∃ γ : ℕ, 0 < γ ∧
      χ hA k = 2 ^ k + (A - 2) * ψ hA k + γ * (4 * A - 5) := by
  have hlt := two_pow_add_mul_psi_lt_chi hA hA3 hk
  have hcong := χ_modEq_pow hA (p := 2) (by norm_num) (by omega) k
  have hmod : 2 * A * 2 - 2 * 2 - 1 = 4 * A - 5 := by omega
  rw [hmod, mul_comm (ψ hA k) (A - 2)] at hcong
  obtain ⟨γ, hγ⟩ := (Nat.modEq_iff_dvd' hlt.le).1 hcong.symm
  have hγpos : 0 < γ := by
    by_contra hn
    have : γ = 0 := by omega
    rw [this, mul_zero] at hγ
    omega
  refine ⟨γ, hγpos, ?_⟩
  rw [mul_comm γ]
  omega

/-- The same quotient equation over `ℤ`, with ordinary signed subtraction. -/
theorem exists_positive_pell_quotient_int {A k : ℕ}
    (hA : 1 < A) (hA3 : 3 ≤ A) (hk : 2 ≤ k) :
    ∃ γ : ℕ, 0 < γ ∧
      (χ hA k : ℤ) = 2 ^ k + ((A : ℤ) - 2) * ψ hA k + γ * (4 * (A : ℤ) - 5) := by
  obtain ⟨γ, hγ, h⟩ := exists_positive_pell_quotient hA hA3 hk
  refine ⟨γ, hγ, ?_⟩
  have h' := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast [Nat.cast_sub (by omega : 2 ≤ A), Nat.cast_sub (by omega : 5 ≤ 4 * A)] at h'
  exact h'

end Jones1982
