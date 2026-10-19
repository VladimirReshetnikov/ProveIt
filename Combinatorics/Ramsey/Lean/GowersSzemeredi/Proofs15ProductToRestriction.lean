import GowersSzemeredi.Proofs14ProductToArrangements
import GowersSzemeredi.Proofs15Restriction

/-!
# From the product property to a dense respected restriction

The exponent estimates of Lemma 15.6 (`lemma156_…`): they retain the
corrected factor `21 * k * 4 ^ (k + 1)` and then use the large final
double-exponential exponent.

The density-lower form of Lemma 15.6 (`lemma_15_6_of_density_lower`), which
uses the selection estimate and the corrected Lemma 14.8 bound, and the
exact-density statement that specializes it (`lemma_15_6_holds`) are in
`Proofs15ProductToRestrictionSide`, outside the final route.

`lemma156_beta_total_exponent`, `lemma156_coefficient_without_density_factor`,
`lemma156_constant_total_exponent`, `lemma156_gamma_total_exponent`,
`lemma156_linear_le_vertex` and `lemma156_scale_ratio_bound` are in
`Proofs15ProductToRestrictionSide`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma lemma156_nat_le_two_pow (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow _ 2 (by norm_num)
      omega

lemma lemma156_beta_base_exponent (k : Nat) (_hk : 1 ≤ k) :
    7 * 4 ^ (k + 1) + 15 ≤ 2 ^ (3 * k + 7) := by
  -- `7 * 4 ^ (k + 1) + 15 ≤ 43 * 4 ^ k ≤ 128 * 8 ^ k`
  have h48 : 4 ^ k ≤ (2 ^ 3) ^ k := Nat.pow_le_pow_left (by norm_num) k
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by norm_num)
  rw [Nat.pow_succ, Nat.pow_add, Nat.pow_mul]
  omega

lemma lemma156_gamma_base_exponent (k : Nat) :
    21 * k * 4 ^ (k + 1) ≤ 2 ^ (3 * k + 7) := by
  have hkpow : k ≤ 2 ^ k := lemma156_nat_le_two_pow k
  have hfour : 4 ^ (k + 1) = 2 ^ (2 * (k + 1)) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  calc
    21 * k * 4 ^ (k + 1) ≤ 2 ^ 5 * 2 ^ k * 2 ^ (2 * (k + 1)) := by
      rw [← hfour]
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (by norm_num : 21 ≤ 2 ^ 5) hkpow) le_rfl
    _ = 2 ^ (3 * k + 7) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

lemma lemma156_constant_base_exponent (k : Nat) :
    46 ≤ 2 ^ (3 * k + 7) := by
  calc
    46 ≤ 2 ^ 7 := by norm_num
    _ ≤ 2 ^ (3 * k + 7) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

end LeanProofs.GowersSzemeredi
