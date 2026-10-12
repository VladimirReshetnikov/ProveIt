import GowersSzemeredi.Proofs13PrintedInitialExtraction

/-! Recover the original printed initial extraction throughout
`0<alpha<=14/15`. Small edge domains use the sharp count; larger edge
domains use adaptive fibre normalization. No extraction conclusion is
assumed, and all original Fourier cutoffs and Bohr radii are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Uniform strong-height Bohr models for every ambient density at most one.
The spectrum, radius, and selected mass are unchanged from the small-density
construction. -/
theorem section13_printed_uniform_height_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hαupper : S.alpha ≤ 14 / 15) :
    let a := S.alpha ^ 32 / 16
    let K := domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta a) Y psi := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  let beta := section13EdgeDensity S h
  have hbounds := section13_edge_density_bounds S h hh
  have ha : 0 < a := div_pos (pow_pos S.alpha_pos _) (by norm_num)
  have hβ : 0 < beta := hbounds.1
  have hβone : beta ≤ 1 := hbounds.2.2.trans S.alpha_at_most_one
  by_cases hsmall : beta ≤ 1 / 6
  · exact section13_printed_uniform_height_model_small_edge S h hh hsmall
  · have hdense : 1 / 6 < beta := lt_of_not_ge hsmall
    let k := Nat.ceil (6 * beta)
    let b := beta / k
    obtain ⟨hk, hbmin, hbmax⟩ := section13_dense_normalization hdense
    have hkR : (0 : Real) < k := by exact_mod_cast hk
    have hkone : (1 : Real) ≤ k := by exact_mod_cast hk
    have hb : 0 < b := div_pos hβ hkR
    have hab : a ≤ b := by
      have hpow := pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one (n := 32)
      dsimp [a]
      linarith only [hpow, hbmin]
    have hcap : N ≤ k * N := by nlinarith only [hk]
    have hcard : ((verticalEdgeDomain S.A h).card : Real) = b * (k * N : Nat) * N := by
      rw [section13_edge_density_card]
      dsimp [b, beta]
      push_cast
      field_simp
    obtain ⟨Y, psi, hY, hmass, hmodel⟩ := section13_good_height_model_with_cap S h hh.2
      (k * N) hcap b hb hbmax hcard
    refine ⟨Y, psi, hY, ?_, ?_⟩
    · have hpow := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 1 / 12) hbmin 6
      have hprod : (1 / 12 : Real) ^ 6 * (1 / 6) ≤ b ^ 6 * beta :=
        mul_le_mul hpow hdense.le (by norm_num) (pow_nonneg hb.le _)
      have hαpow := pow_le_pow_left₀ S.alpha_pos.le hαupper 128
      norm_num at hαpow
      have hcoeff : (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 ≤ b ^ 6 * beta / 20000 := by
        norm_num [zpow_neg] at hprod ⊢
        nlinarith only [hprod, hαpow]
      calc
        _ ≤ b ^ 6 * beta / 20000 * (N : Real) ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
        _ = b ^ 6 * (verticalEdgeDomain S.A h).card / 20000 := by
          rw [section13_edge_density_card]
          dsimp [beta]
          ring
        _ ≤ Y.card := hmass
    · apply bohr_difference_model_restrict _ _ _ _ _ _ _ _ hmodel
      apply bohr_domain_mono ?_ (section10Zeta_mono ha hab (hbmax.trans (by norm_num)))
      intro r hr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hlam : section10Lambda a ≤ section10Lambda b := by
        unfold section10Lambda
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hab (by norm_num)) (by positivity)
      have hcapR : (N : Real) ≤ (k * N : Nat) := by exact_mod_cast hcap
      have hlampos : 0 ≤ section10Lambda b := by unfold section10Lambda; positivity
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul hlam hcapR (Nat.cast_nonneg _) hlampos) (Nat.cast_nonneg N)).trans
          (Finset.mem_filter.mp hr).2

/-- Stage 13.6 from the preceding stages and explicit numerical budgets.
All row subsets and Bohr models are constructed; only the density range and
integer/radius inequalities remain as hypotheses. The upper progression
length is preserved for the later coefficient extraction. -/
theorem lemma_13_6_printed_from_initial_stages_wider {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (hαupper : S.alpha ≤ 14 / 15)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  let K : ZMod N → Finset (ZMod N) := fun h ↦
    domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
  have hex : ∀ h : ZMod N, ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      h ∈ criticalHeights S D E →
        Y ⊆ verticalEdgeDomain S.A h ∧
        (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤ Y.card ∧
        HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
          (K h) (section10Zeta a) Y psi := by
    intro h
    by_cases hh : h ∈ criticalHeights S D E
    · obtain ⟨Y, psi, hdata⟩ := section13_printed_uniform_height_model S h
        (Finset.mem_filter.mp hh).2 hαupper
      exact ⟨Y, psi, fun _ ↦ hdata⟩
    · exact ⟨∅, fun _ ↦ 0, fun hh' ↦ (hh hh').elim⟩
  choose Y psi hdata using hex
  apply lemma_13_6_printed_of_bohr_models_with_length S (section10Lambda a) (section10Zeta a) D E m Y K psi
    h134 h135 hm hsize hupper hlower
    (fun h hh ↦ ⟨(hdata h hh).1, (hdata h hh).2.1⟩) ?_ hbudget
    (fun h hh ↦ (hdata h hh).2.2)
  intro h hh r hr
  have hthreshold := (Finset.mem_filter.mp hr).2
  change section10Lambda a * N * N ≤
    ‖fourier (domainFibreCountFunction (section13VerticalDomain S.A h)) r‖ at hthreshold
  rw [section13_vertical_fibre_function] at hthreshold
  convert hthreshold using 1 <;> ring

theorem lemma_13_6_printed_improved_length_wider {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E) (hαupper : S.alpha ≤ 14 / 15) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧
      section13Zeta S.alpha / 2 *
        (N : Real) ^ ((1 : Real) / (2 : Real) ^ (10 * section13Q S.alpha)) ≤ F.R.length ∧
      F.R.length ≤ max 1 E.Q.length := by
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
  · obtain ⟨m, hm, hsize, hupper, hlower, hbohr⟩ := section13_ten_integer_budgets
      S.alpha_pos S.alpha_at_most_one N D.q D.m D.P.length E.Q.length hN h134.1
      h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1 h135.2.2.2.1 (lt_of_not_ge hs).le
    obtain ⟨F, hF, hmR, hRupper⟩ := lemma_13_6_printed_from_initial_stages_wider
      S D E m hαupper h134 h135 hm hsize hupper (htarget.trans hlower) hbohr
    exact ⟨F, hF, hlower.trans (Nat.cast_le.mpr hmR), hRupper.trans (le_max_right _ _)⟩

/-- Original printed masses and length bound in the explicit small-density
range. The construction in fact supplies the stronger `10Q` length exponent. -/
def lemma_13_6_printed_wider_density : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N),
    Nat.Prime N → S.alpha ≤ 14 / 15 →
    IsStage134Data S ((2 : Real) ^ (-(59 : Int)) * S.alpha ^ 176) D →
    IsStage135Data S D E →
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F

theorem lemma_13_6_printed_wider_density_holds : lemma_13_6_printed_wider_density := by
  intro N _ S D E hprime hαupper h134 h135
  obtain ⟨F, hF, _, _⟩ := lemma_13_6_printed_improved_length_wider hprime S D E
    (by simpa only [section13_lambda_formula S.alpha_pos] using h134) h135 hαupper
  exact ⟨F, hF⟩

end LeanProofs.GowersSzemeredi
