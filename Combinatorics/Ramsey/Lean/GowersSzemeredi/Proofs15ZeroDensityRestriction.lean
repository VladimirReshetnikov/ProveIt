import GowersSzemeredi.Proofs14ZeroProductArrangements
import GowersSzemeredi.Proofs15LowerDensityRestriction

/-! The missing height-zero case of density-uniform product restriction.
Together with the higher-dimensional argument this covers every natural k. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma156_zero_coefficient {beta gamma : Real}
    (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (beta * gamma / 2) ^ (2 ^ (2 ^ (0 + 5))) ≤
      (beta ^ 28 * gamma ^ 56 * ((2 : Real)⁻¹ ^ 44) / 4) ^ arrangementSelectionExponent 0 := by
  let S := arrangementSelectionExponent 0
  let T := (2 : Nat) ^ (2 ^ (0 + 5))
  have hbeta : 28 * S ≤ T := by norm_num [S, T, arrangementSelectionExponent]
  have hgamma : 56 * S ≤ T := by norm_num [S, T, arrangementSelectionExponent]
  have hconstant : 46 * S ≤ T := by norm_num [S, T, arrangementSelectionExponent]
  have hbp : beta ^ T ≤ beta ^ (28 * S) := pow_le_pow_of_le_one hb.le hb1 hbeta
  have hgp : gamma ^ T ≤ gamma ^ (56 * S) := pow_le_pow_of_le_one hg.le hg1 hgamma
  have hcp : ((2 : Real)⁻¹) ^ T ≤ ((2 : Real)⁻¹) ^ (46 * S) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hconstant
  have hnum : (2 : Real)⁻¹ ^ 44 / 4 = (2 : Real)⁻¹ ^ 46 := by norm_num
  calc
    (beta * gamma / 2) ^ T = beta ^ T * gamma ^ T * ((2 : Real)⁻¹) ^ T := by
      rw [div_eq_mul_inv, mul_pow, mul_pow]
    _ ≤ beta ^ (28 * S) * gamma ^ (56 * S) * ((2 : Real)⁻¹) ^ (46 * S) := by
      exact mul_le_mul (mul_le_mul hbp hgp (by positivity) (by positivity))
        hcp (by positivity) (by positivity)
    _ = (beta ^ 28 * gamma ^ 56 * ((2 : Real)⁻¹ ^ 44) / 4) ^ S := by
      rw [show beta ^ 28 * gamma ^ 56 * ((2 : Real)⁻¹ ^ 44) / 4 =
        (beta ^ 28 * gamma ^ 56) * ((2 : Real)⁻¹ ^ 44 / 4) by ring, hnum,
        mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]

theorem lemma_15_6_zero_of_density_lower (beta gamma : Real)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      ∀ (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N),
        beta * (N : Real) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N 1), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (0 + 5))) * (N : Real) ^ 15 ≤ generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  let alpha := beta ^ 28 * gamma ^ 56
  let eta := (2 : Real)⁻¹ ^ 44
  have ha : 0 < alpha := mul_pos (pow_pos hb _) (pow_pos hg _)
  have he : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ := selection_scale_estimate_zero alpha 1 eta ha (by norm_num) he he1
  refine ⟨N0, ?_⟩
  intro N _ hN B phi hB hprod
  have hNp : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let b : Real := (B.card : Real) / N
  have hbb : beta ≤ b := (le_div_iff₀ hNp).mpr hB
  have hbpos : 0 < b := hb.trans_le hbb
  have hcard : (B.card : Real) = b * (N : Real) ^ (0 + 1 : Nat) := by
    simp only [Nat.zero_add, pow_one]
    dsimp [b]
    field_simp
  have hbupper : b ≤ 1 := by
    apply (div_le_one hNp).mpr
    exact_mod_cast (show B.card ≤ N by
      simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hu : (generalArrangementCount 8 B : Real) ≤ 1 * (N : Real) ^ 15 := by
    exact (selection_arrangement_real_upper b B hcard).trans
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbpos.le hbupper) (by positivity))
  have hl : alpha * 1 * (N : Real) ^ 15 ≤ respectedGeneralArrangementCount 8 B phi := by
    simpa only [mul_one] using productProperty_zero_eight_arrangements B phi hb hg hB hprod
  obtain ⟨B', hsub, hcount, hrespect⟩ := hN0 N hN B phi hu hl
  refine ⟨B', hsub, ?_, hrespect⟩
  exact (mul_le_mul_of_nonneg_right (lemma156_zero_coefficient hb hb1 hg hg1)
    (by positivity)).trans (by simpa only [alpha, eta, mul_one] using hcount)

theorem lemma_15_6_of_density_lower_all (k : Nat) (beta gamma : Real)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        beta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) * (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨N0, hN0⟩ := lemma_15_6_zero_of_density_lower beta gamma hb hb1 hg hg1
    refine ⟨N0, ?_⟩
    intro N _ hN _ _ B phi hB hprod
    exact hN0 N hN B phi (by simpa using hB) hprod
  · exact lemma_15_6_of_density_lower k beta gamma (by omega) hb hb1 hg hg1

end LeanProofs.GowersSzemeredi
