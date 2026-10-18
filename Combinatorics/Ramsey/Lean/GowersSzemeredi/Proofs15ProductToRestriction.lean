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

private lemma lemma156_linear_le_vertex (k : Nat) :
    4 * k + 10 ≤ 2 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k + 1 + 4 = (k + 4) + 1 by omega, pow_succ]
      omega

private lemma lemma156_scale_ratio_bound (k : Nat) :
    2 ^ (3 * k + 7) * arrangementSelectionExponent k ≤
      2 ^ (2 ^ (k + 5)) := by
  unfold arrangementSelectionExponent
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have hlinear := lemma156_linear_le_vertex k
  have hdouble : 2 * 2 ^ (k + 4) = 2 ^ (k + 5) := by
    calc
      2 * 2 ^ (k + 4) = 2 ^ (k + 4) * 2 := Nat.mul_comm _ _
      _ = 2 ^ ((k + 4) + 1) := (pow_succ 2 (k + 4)).symm
      _ = 2 ^ (k + 5) := by congr 1
  rw [← hdouble]
  omega

lemma lemma156_beta_base_exponent (k : Nat) (hk : 1 ≤ k) :
    7 * 4 ^ (k + 1) + 15 ≤ 2 ^ (3 * k + 7) := by
  have hfour : 4 ^ (k + 1) = 2 ^ (2 * (k + 1)) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hA : 7 * 4 ^ (k + 1) ≤ 2 ^ (2 * k + 5) := by
    calc
      7 * 4 ^ (k + 1) = 7 * 2 ^ (2 * (k + 1)) := by rw [hfour]
      _ ≤ 2 ^ 3 * 2 ^ (2 * (k + 1)) :=
        Nat.mul_le_mul_right _ (by norm_num : 7 ≤ 2 ^ 3)
      _ = 2 ^ (2 * k + 5) := by
        rw [← pow_add]
        congr 1
        omega
  have h15 : 15 ≤ 2 ^ (2 * k + 5) := by
    calc
      15 ≤ 2 ^ 7 := by norm_num
      _ ≤ 2 ^ (2 * k + 5) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : 7 * 4 ^ (k + 1) + 15 ≤ 2 ^ (2 * k + 6) := by
    calc
      7 * 4 ^ (k + 1) + 15 ≤
          2 ^ (2 * k + 5) + 2 ^ (2 * k + 5) := Nat.add_le_add hA h15
      _ = 2 ^ (2 * k + 6) := by
        calc
          2 ^ (2 * k + 5) + 2 ^ (2 * k + 5) =
              2 ^ (2 * k + 5) * 2 := by omega
          _ = 2 ^ ((2 * k + 5) + 1) :=
            (pow_succ 2 (2 * k + 5)).symm
          _ = 2 ^ (2 * k + 6) := by congr 1
  exact hsum.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

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

lemma lemma156_beta_total_exponent (k : Nat) (hk : 1 ≤ k) :
    7 * 4 ^ (k + 1) * arrangementSelectionExponent k + 15 ≤
      2 ^ (2 ^ (k + 5)) := by
  let S := arrangementSelectionExponent k
  let R := 2 ^ (3 * k + 7)
  have hS : 1 ≤ S := by
    dsimp only [S, arrangementSelectionExponent]
    exact Nat.one_le_pow _ 2 (by norm_num)
  have hbase := lemma156_beta_base_exponent k hk
  have hfirst : 7 * 4 ^ (k + 1) * S + 15 ≤
      (7 * 4 ^ (k + 1) + 15) * S := by
    nlinarith
  calc
    7 * 4 ^ (k + 1) * arrangementSelectionExponent k + 15 ≤
        (7 * 4 ^ (k + 1) + 15) * S := hfirst
    _ ≤ R * S := Nat.mul_le_mul_right S hbase
    _ ≤ 2 ^ (2 ^ (k + 5)) := lemma156_scale_ratio_bound k

lemma lemma156_gamma_total_exponent (k : Nat) :
    21 * k * 4 ^ (k + 1) * arrangementSelectionExponent k ≤
      2 ^ (2 ^ (k + 5)) := by
  exact (Nat.mul_le_mul_right _ (lemma156_gamma_base_exponent k)).trans
    (lemma156_scale_ratio_bound k)

lemma lemma156_constant_total_exponent (k : Nat) :
    46 * arrangementSelectionExponent k ≤ 2 ^ (2 ^ (k + 5)) := by
  exact (Nat.mul_le_mul_right _ (lemma156_constant_base_exponent k)).trans
    (lemma156_scale_ratio_bound k)

theorem lemma156_coefficient_without_density_factor (k : Nat) (hk : 1 ≤ k)
    {beta gamma : Real} (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) ≤
      (beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)) *
        ((2 : Real)⁻¹ ^ 44) / 4) ^ arrangementSelectionExponent k := by
  let A := 7 * 4 ^ (k + 1)
  let G := 21 * k * 4 ^ (k + 1)
  let S := arrangementSelectionExponent k
  let T := 2 ^ (2 ^ (k + 5))
  have hbeta : A * S ≤ T := by
    have h := lemma156_beta_total_exponent k hk
    dsimp [A, S, T]
    omega
  have hgamma : G * S ≤ T := lemma156_gamma_total_exponent k
  have hconstant : 46 * S ≤ T := lemma156_constant_total_exponent k
  have hbp : beta ^ T ≤ beta ^ (A * S) := pow_le_pow_of_le_one hb.le hb1 hbeta
  have hgp : gamma ^ T ≤ gamma ^ (G * S) := pow_le_pow_of_le_one hg.le hg1 hgamma
  have hcp : ((2 : Real)⁻¹) ^ T ≤ ((2 : Real)⁻¹) ^ (46 * S) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hconstant
  have hnum : (2 : Real)⁻¹ ^ 44 / 4 = (2 : Real)⁻¹ ^ 46 := by norm_num
  calc
    (beta * gamma / 2) ^ T = beta ^ T * gamma ^ T * ((2 : Real)⁻¹) ^ T := by
      rw [div_eq_mul_inv, mul_pow, mul_pow]
    _ ≤ beta ^ (A * S) * gamma ^ (G * S) * ((2 : Real)⁻¹) ^ (46 * S) := by
      exact mul_le_mul (mul_le_mul hbp hgp (by positivity) (by positivity))
        hcp (by positivity) (by positivity)
    _ = (beta ^ A * gamma ^ G * ((2 : Real)⁻¹ ^ 44) / 4) ^ S := by
      rw [show beta ^ A * gamma ^ G * ((2 : Real)⁻¹ ^ 44) / 4 =
        (beta ^ A * gamma ^ G) * ((2 : Real)⁻¹ ^ 44 / 4) by ring, hnum,
        mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]

end LeanProofs.GowersSzemeredi
