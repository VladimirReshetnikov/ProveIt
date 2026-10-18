import GowersSzemeredi.Proofs15FejerProduct

/-! Declarations of `Proofs15FejerProduct` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

theorem fejer_product_restriction : FejerProductRestriction := by
  unfold FejerProductRestriction
  intro k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  let A : Nat := 7 * 4 ^ (k + 1)
  let G : Nat := 21 * k * 4 ^ (k + 1)
  let S : Nat := fejerSelectionExponent k
  let T : Nat := fejerProductExponent k
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
  obtain ⟨N0, hN0⟩ := fejer_arrangement_restriction k alpha beta eta hk halpha
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
    have hS1 : 1 ≤ S := by
      dsimp only [S, fejerSelectionExponent]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc A * S + 15 ≤ (A + 15) * S := by nlinarith
      _ ≤ 2 ^ (3 * k + 7) * S := Nat.mul_le_mul_right S (lemma156_beta_base_exponent k hk)
      _ = T := rfl
  have hgammaExponent : G * S ≤ T := Nat.mul_le_mul_right S (lemma156_gamma_base_exponent k)
  have hconstantExponent : 46 * S ≤ T := Nat.mul_le_mul_right S (lemma156_constant_base_exponent k)
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
      (beta * gamma / 2) ^ fejerProductExponent k *
          (N : Real) ^ (17 * k + 15) =
          (beta * gamma / 2) ^ T *
            (N : Real) ^ (17 * k + 15) := by rfl
      _ ≤ ((alpha * eta / 4) ^ S * beta ^ 15) *
            (N : Real) ^ (17 * k + 15) :=
        mul_le_mul_of_nonneg_right hcoefficient hNpow0
      _ ≤ generalArrangementCount 8 B' := by
        simpa only [S, mul_assoc] using hraw
  · simpa only [eta] using hdensity

/-- **The Fejér Lemma 15.6 implies the printed Lemma 15.6.** -/
theorem lemma_15_6_of_fejer_product (h : FejerProductRestriction) : lemma_15_6 := by
  intro k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  obtain ⟨N0, hN0⟩ := h k beta gamma hk hbeta hbeta_one hgamma hgamma_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hproduct
  obtain ⟨B', hB'B, hlower, hdens⟩ := hN0 N hN hprime hodd B phi hBcard hproduct
  refine ⟨B', hB'B, le_trans ?_ hlower, hdens⟩
  have hexp : fejerProductExponent k ≤ 2 ^ (2 ^ (k + 5)) := by
    refine (fejerProductExponent_le k).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have := Nat.lt_two_pow_self (n := k)
    have e : 2 ^ (k + 5) = 32 * 2 ^ k := by rw [pow_add]; ring
    rw [e]
    omega
  have hbase0 : 0 ≤ beta * gamma / 2 := by positivity
  have hbase1 : beta * gamma / 2 ≤ 1 := by
    have := mul_le_mul hbeta_one hgamma_one hgamma.le zero_le_one
    linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hbase0 hbase1 hexp) (by positivity)

/-- **The Fejér Lemma 15.6 with a density lower bound**: the threshold depends
only on a lower bound `β` for the density of `B`. This is the form that
Lemma 16.4 consumes (`lemma_15_6_of_density_lower`), with
`fejerProductExponent k ≤ 2^(5k+14)` in place of `2^(2^(k+5))`. -/
theorem fejer_product_of_density_lower (k : Nat) (beta gamma : Real)
    (hk : 1 ≤ k) (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        beta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ fejerProductExponent k * (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  let alpha := beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1))
  let eta := (2 : Real)⁻¹ ^ 44
  have ha : 0 < alpha := mul_pos (pow_pos hb _) (pow_pos hg _)
  have he : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := fejer_scale_estimate k alpha 1 eta hk ha (by norm_num) he he1
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
  have hcoef := fejer_coefficient_without_density_factor k hk hb hb1 hg hg1
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
    (by simpa [alpha, eta] using hcount)

end LeanProofs.GowersSzemeredi
