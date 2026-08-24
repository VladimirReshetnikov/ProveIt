import GowersSzemeredi.Proofs14ProductToArrangements
import GowersSzemeredi.Proofs15Restriction

/-!
# From the product property to a dense respected restriction

This file proves Lemma 15.6 by applying Lemma 15.5 to the corrected
Lemma 14.8 lower bound.  The elementary exponent estimates below retain the
corrected factor `21 * k * 4 ^ (k + 1)` and then exploit the very large final
double-exponential exponent.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma lemma156_nat_le_two_pow (k : Nat) : k ≤ 2 ^ k := by
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
      have hpow : 4 ≤ 2 ^ (k + 4) := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
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

private lemma lemma156_beta_base_exponent (k : Nat) (hk : 1 ≤ k) :
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

private lemma lemma156_gamma_base_exponent (k : Nat) :
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

private lemma lemma156_constant_base_exponent (k : Nat) :
    46 ≤ 2 ^ (3 * k + 7) := by
  calc
    46 ≤ 2 ^ 7 := by norm_num
    _ ≤ 2 ^ (3 * k + 7) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma lemma156_beta_total_exponent (k : Nat) (hk : 1 ≤ k) :
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

private lemma lemma156_gamma_total_exponent (k : Nat) :
    21 * k * 4 ^ (k + 1) * arrangementSelectionExponent k ≤
      2 ^ (2 ^ (k + 5)) := by
  exact (Nat.mul_le_mul_right _ (lemma156_gamma_base_exponent k)).trans
    (lemma156_scale_ratio_bound k)

private lemma lemma156_constant_total_exponent (k : Nat) :
    46 * arrangementSelectionExponent k ≤ 2 ^ (2 ^ (k + 5)) := by
  exact (Nat.mul_le_mul_right _ (lemma156_constant_base_exponent k)).trans
    (lemma156_scale_ratio_bound k)

/-- **Lemma 15.6.** Product structure yields a large restriction on which
almost all eight-arrangements are respected. -/
theorem lemma_15_6_holds : lemma_15_6 := by
  unfold lemma_15_6
  intro k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  let A : Nat := 7 * 4 ^ (k + 1)
  let G : Nat := 21 * k * 4 ^ (k + 1)
  let S : Nat := arrangementSelectionExponent k
  let T : Nat := 2 ^ (2 ^ (k + 5))
  let alpha : Real := beta ^ A * gamma ^ G
  let eta : Real := ((2 : Real)⁻¹) ^ 44
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    exact mul_pos (pow_pos hbeta _) (pow_pos hgamma _)
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have heta_one : eta ≤ 1 := by
    dsimp only [eta]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := lemma_15_5_holds k alpha beta eta hk halpha
    hbeta heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hproduct
  have hfromProduct := lemma_14_8_holds N k beta gamma B phi hk hbeta
    hgamma hgamma_one hBcard hproduct
  have hbeta15 : beta ^ 15 ≤ 1 :=
    pow_le_one₀ hbeta.le hbeta_one
  have hNpow0 : 0 ≤ (N : Real) ^ (17 * k + 15) := by positivity
  have hinput :
      alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
        respectedGeneralArrangementCount 8 B phi := by
    calc
      alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
          alpha * 1 * (N : Real) ^ (17 * k + 15) := by
        gcongr
      _ = beta ^ (7 * 4 ^ (k + 1)) *
            gamma ^ (21 * k * 4 ^ (k + 1)) *
              (N : Real) ^ (17 * k + 15) := by
        dsimp only [alpha, A, G]
        ring
      _ ≤ respectedGeneralArrangementCount 8 B phi := hfromProduct
  obtain ⟨B', hB'B, hraw, hdensity⟩ :=
    hN0 N hN hprime hodd B phi hBcard hinput
  have hbetaExponent :
      A * S + 15 ≤ T := by
    exact lemma156_beta_total_exponent k hk
  have hgammaExponent : G * S ≤ T := by
    exact lemma156_gamma_total_exponent k
  have hconstantExponent : 46 * S ≤ T := by
    exact lemma156_constant_total_exponent k
  have hbetaPow : beta ^ T ≤ beta ^ (A * S + 15) :=
    pow_le_pow_of_le_one hbeta.le hbeta_one hbetaExponent
  have hgammaPow : gamma ^ T ≤ gamma ^ (G * S) :=
    pow_le_pow_of_le_one hgamma.le hgamma_one hgammaExponent
  have hhalfPow :
      ((2 : Real)⁻¹) ^ T ≤ ((2 : Real)⁻¹) ^ (46 * S) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hconstantExponent
  have hnumeric : eta / 4 = ((2 : Real)⁻¹) ^ 46 := by
    dsimp only [eta]
    norm_num
  have hexact :
      (alpha * eta / 4) ^ S * beta ^ 15 =
        beta ^ (A * S + 15) * gamma ^ (G * S) *
          ((2 : Real)⁻¹) ^ (46 * S) := by
    calc
      (alpha * eta / 4) ^ S * beta ^ 15 =
          (alpha * (eta / 4)) ^ S * beta ^ 15 := by ring
      _ = ((beta ^ A * gamma ^ G) * ((2 : Real)⁻¹) ^ 46) ^ S *
          beta ^ 15 := by rw [hnumeric]
      _ = (beta ^ (A * S) * beta ^ 15) * gamma ^ (G * S) *
          ((2 : Real)⁻¹) ^ (46 * S) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
        ring
      _ = beta ^ (A * S + 15) * gamma ^ (G * S) *
          ((2 : Real)⁻¹) ^ (46 * S) := by rw [pow_add]
  have hcoarse :
      (beta * gamma / 2) ^ T =
        beta ^ T * gamma ^ T * ((2 : Real)⁻¹) ^ T := by
    rw [div_eq_mul_inv, mul_pow, mul_pow]
  have hcoefficient :
      (beta * gamma / 2) ^ T ≤
        (alpha * eta / 4) ^ S * beta ^ 15 := by
    rw [hcoarse, hexact]
    have hbg : beta ^ T * gamma ^ T ≤
        beta ^ (A * S + 15) * gamma ^ (G * S) :=
      mul_le_mul hbetaPow hgammaPow (pow_nonneg hgamma.le _)
        (pow_nonneg hbeta.le _)
    exact mul_le_mul hbg hhalfPow (pow_nonneg (by norm_num) _)
      (mul_nonneg (pow_nonneg hbeta.le _) (pow_nonneg hgamma.le _))
  refine ⟨B', hB'B, ?_, ?_⟩
  · calc
      (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) *
          (N : Real) ^ (17 * k + 15) =
          (beta * gamma / 2) ^ T *
            (N : Real) ^ (17 * k + 15) := by rfl
      _ ≤ ((alpha * eta / 4) ^ S * beta ^ 15) *
            (N : Real) ^ (17 * k + 15) :=
        mul_le_mul_of_nonneg_right hcoefficient hNpow0
      _ ≤ generalArrangementCount 8 B' := by
        simpa only [S, mul_assoc] using hraw
  · simpa only [eta] using hdensity

end LeanProofs.GowersSzemeredi
