import GowersSzemeredi.Proofs14ProductToArrangements
import GowersSzemeredi.Proofs15Restriction

/-!
# From the product property to a dense respected restriction

The density-lower form of Lemma 15.6 uses the selection estimate and the
corrected Lemma 14.8 bound; the exact-density statement specializes it.
The exponent estimates retain the corrected factor `21 * k * 4 ^ (k + 1)`
and then use the large final double-exponential exponent.
-/

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

theorem lemma_15_6_of_density_lower (k : Nat) (beta gamma : Real)
    (hk : 1 ≤ k) (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        beta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) * (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  let alpha := beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1))
  let eta := (2 : Real)⁻¹ ^ 44
  have ha : 0 < alpha := mul_pos (pow_pos hb _) (pow_pos hg _)
  have he : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := selection_scale_estimate k alpha 1 eta hk ha (by norm_num) he he1
  refine ⟨N0, ?_⟩
  intro N _ hN hp ho B phi hB hprod
  have hNp : 0 < (N : Real) ^ (k + 1) := pow_pos (by exact_mod_cast NeZero.pos N) _
  let b : Real := (B.card : Real) / (N : Real) ^ (k + 1)
  have hbb : beta ≤ b := (le_div_iff₀ hNp).mpr hB
  have hbpos : 0 < b := hb.trans_le hbb
  have hcard : (B.card : Real) = b * (N : Real) ^ (k + 1) := by
    dsimp [b]
    field_simp
  have hbupper : b ≤ 1 := by
    apply (div_le_one hNp).mpr
    exact_mod_cast (show B.card ≤ N ^ (k + 1) by
      simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hu : (generalArrangementCount 8 B : Real) ≤ 1 * (N : Real) ^ (17 * k + 15) := by
    exact (selection_arrangement_real_upper b B hcard).trans
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbpos.le hbupper) (by positivity))
  have hl : alpha * 1 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi := by
    have hc := lemma_14_8_holds N k b gamma B phi hk hbpos hg hg1 hcard hprod
    apply le_trans ?_ hc
    dsimp [alpha]
    simp only [mul_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le hbb _)
        (pow_nonneg hg.le _)) (by positivity)
  obtain ⟨B', hsub, hcount, hrespect⟩ := hN0 N hN hp ho B phi hu hl
  refine ⟨B', hsub, ?_, hrespect⟩
  have hcoef := lemma156_coefficient_without_density_factor k hk hb hb1 hg hg1
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans (by simpa [alpha, eta] using hcount)

/-- **Lemma 15.6.** Product structure yields a large restriction on which
almost all eight-arrangements are respected. -/
theorem lemma_15_6_holds : lemma_15_6 := by
  intro k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  obtain ⟨N0, hN0⟩ :=
    lemma_15_6_of_density_lower k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hproduct
  exact hN0 N hN hprime hodd B phi hBcard.ge hproduct

end LeanProofs.GowersSzemeredi
