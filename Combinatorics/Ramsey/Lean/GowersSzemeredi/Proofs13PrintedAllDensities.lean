import GowersSzemeredi.Proofs13PrintedWiderExtraction
import GowersSzemeredi.Proofs13DenseEdgePiece

/-! The original printed masses in Lemma13.6 at every density and scale.
The dense bilinear piece supplies the previously missing larger-density case. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13Zeta_le_half {alpha : Real} (ha : 0 < alpha) (haone : alpha ≤ 1) :
    section13Zeta alpha ≤ 1 / 2 := by
  have hi : (1 : Real) ≤ alpha ^ (-(320 : Int)) := by
    simp only [zpow_neg]
    have hp : alpha ^ (320 : Nat) ≤ 1 := pow_le_one₀ ha.le haone
    have hz : alpha ^ (320 : Nat) ≠ 0 := pow_ne_zero _ ha.ne'
    calc
      1 = (alpha ^ (320 : Nat))⁻¹ * alpha ^ (320 : Nat) := (inv_mul_cancel₀ hz).symm
      _ ≤ (alpha ^ (320 : Nat))⁻¹ * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (alpha ^ (320 : Nat))⁻¹ := mul_one _
  have hk : (1 : Real) ≤ section13K alpha := by
    calc
      _ ≤ (2 : Real) ^ 114 * 1 := by norm_num
      _ ≤ (2 : Real) ^ 114 * alpha ^ (-(320 : Int)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = section13K alpha := rfl
  have hfirst : (2 : Real) ^ (-(228 * section13K alpha)) ≤ 1 / 2 := by
    calc
      _ ≤ (2 : Real) ^ (-(1 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num [Real.rpow_neg]
  have hsecond : alpha ^ (576 * section13K alpha) ≤ 1 :=
    Real.rpow_le_one ha.le haone (by linarith)
  unfold section13Zeta
  calc
    _ ≤ (2 : Real) ^ (-(228 * section13K alpha)) * 1 :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ ≤ 1 / 2 := by simpa using hfirst

theorem section13_ten_target_le_one_small_modulus {alpha : Real}
    (ha : 0 < alpha) (haone : alpha ≤ 1) {N : Nat} (hN : 1 ≤ N) (hsmall : N ≤ 4) :
    section13Zeta alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q alpha)) ≤ 1 := by
  have hQ : 0 ≤ section13Q alpha := by unfold section13Q; positivity
  have he : (1 : Real) / (2 : Real) ^ (10 * section13Q alpha) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hpow : (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q alpha)) ≤ N :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hN) he
  have hz := section13Zeta_le_half ha haone
  calc
    _ ≤ (1 / 4 : Real) * N := mul_le_mul (by linarith) hpow (by positivity) (by norm_num)
    _ ≤ 1 := by
      have hN4 : (N : Real) ≤ 4 := by exact_mod_cast hsmall
      linarith

theorem lemma_13_6_printed_high_density_from_budgets {N : Nat} [Fact N.Prime]
    (hN : 5 ≤ N) (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (hα : 14 / 15 < S.alpha) (h135 : IsStage135Data S D E) (m : Nat)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧
      m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨Y, c, hY⟩ := section13_printed_high_density_edge_rules hN S hα
  apply lemma_13_6_printed_of_short_difference_rules_with_length S D E h135 m Y
    hm hsize hupper hlower (fun h _ ↦ ⟨(hY h).1, (hY h).2.1⟩)
  intro h _
  exact ⟨c * h, fun v hv w hw _ ↦ (hY h).2.2 v hv w hw⟩

/-- The original printed extraction, with a strictly stronger length
exponent, now follows from the actual preceding data at every density. -/
theorem lemma_13_6_printed_all_densities_improved_length {N : Nat} [NeZero N]
    (hprime : N.Prime) (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧
      section13Zeta S.alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q S.alpha)) ≤ F.R.length ∧
      F.R.length ≤ max 1 E.Q.length := by
  by_cases hlow : S.alpha ≤ 14 / 15
  · exact lemma_13_6_printed_improved_length_wider hprime S D E h134 h135 hlow
  have hα : 14 / 15 < S.alpha := lt_of_not_ge hlow
  letI : Fact N.Prime := ⟨hprime⟩
  have hN : 1 ≤ N := by have := hprime.two_le; omega
  have htarget := section13_row_target_antitone S.alpha_pos N hN (by norm_num : (10 : Real) ≤ 13)
  by_cases hs : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q S.alpha)) ≤ 1
  · obtain ⟨F, hF, hlen⟩ := lemma_13_6_printed_small_row_scale_with_length S D E h135 (htarget.trans hs)
    refine ⟨F, hF, ?_, ?_⟩
    · simpa only [hlen, Nat.cast_one] using hs
    · rw [hlen]
      exact le_max_left _ _
  have hNfive : 5 ≤ N := by
    by_contra h
    exact hs (section13_ten_target_le_one_small_modulus S.alpha_pos S.alpha_at_most_one hN (by omega))
  obtain ⟨m, hm, hsize, hupper, hlower, _⟩ := section13_ten_integer_budgets
    S.alpha_pos S.alpha_at_most_one N D.q D.m D.P.length E.Q.length hN h134.1
    h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1 h135.2.2.2.1 (lt_of_not_ge hs).le
  obtain ⟨F, hF, hmR, hRupper⟩ := lemma_13_6_printed_high_density_from_budgets
    hNfive S D E hα h135 m hm hsize hupper (htarget.trans hlower)
  exact ⟨F, hF, hlower.trans (Nat.cast_le.mpr hmR), hRupper.trans (le_max_right _ _)⟩

def lemma_13_6_printed_bounds : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N),
    Nat.Prime N →
    IsStage134Data S ((2 : Real) ^ (-(59 : Int)) * S.alpha ^ 176) D →
    IsStage135Data S D E →
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F

theorem lemma_13_6_printed_bounds_holds : lemma_13_6_printed_bounds := by
  intro N _ S D E hprime h134 h135
  obtain ⟨F, hF, _, _⟩ := lemma_13_6_printed_all_densities_improved_length hprime S D E
    (by simpa only [section13_lambda_formula S.alpha_pos] using h134) h135
  exact ⟨F, hF⟩

end LeanProofs.GowersSzemeredi
