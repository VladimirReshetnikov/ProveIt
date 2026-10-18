import GowersSzemeredi.Proofs13SharpEdgeDensity
import GowersSzemeredi.Proofs13PrintedRowBounds
import GowersSzemeredi.Proofs13SmallRowScale
import GowersSzemeredi.Proofs13TenRowBudgets
import GowersSzemeredi.Proofs13CommonStepSelectionSide

/-! The original printed Lemma 13.6 masses from the actual preceding data
throughout the small-density range, without an additional modulus threshold.
The sharp edge count supplies the mass; no stronger extraction is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Assemble Stage 13.6 from its row models and explicit integer partition
budgets, retaining the upper length bound needed by Lemma 13.9. -/
theorem lemma_13_6_printed_of_short_difference_rules_with_length {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h135 : IsStage135Data S D E) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤ (Y h).card)
    (hrule : ∀ h ∈ criticalHeights S D E, ∃ c : ZMod N, ∀ v ∈ Y h, ∀ w ∈ Y h,
      v.1 - w.1 ∈ section10SymmetricMultiples E.Q.step m →
        verticalPhiDifference S.phi h v - verticalPhiDifference S.phi h w =
          c * (v.1 - w.1)) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  classical
  let delta : Real := (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128
  obtain ⟨R, hs, hp, hl, hlinear, hmass⟩ := common_step_row_selection
    (criticalHeights S D E) Y (verticalPhiDifference S.phi) E.Q.step m delta
    h135.1 hm hsize (fun h hh ↦ (hY h hh).2) hrule
  have hmR : m ≤ R.length := by rcases hl with h | h <;> omega
  have hRupper : R.length ≤ E.Q.length := by rcases hl with h | h <;> omega
  have hRlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ R.length :=
    hlower.trans (by exact_mod_cast hmR)
  let F : Stage136Data N := ⟨R, Y⟩
  have hα : 0 ≤ S.alpha := S.alpha_pos.le
  have hI := h135.2.2.2.2.2
  have hIweak : S.alpha ^ 32 * E.Q.length / 32 ≤ (criticalHeights S D E).card := by
    have hnonneg : 0 ≤ S.alpha ^ 32 * E.Q.length := by positivity
    linarith
  refine ⟨F, ⟨hs, ?_, hp, hRlower, ?_, hmass, ?_⟩, hmR, hRupper⟩
  · change R.step != 0
    rw [hs]
    exact h135.1
  · intro h hh
    exact ⟨(hY h hh).1, (hY h hh).2, hlinear h hh⟩
  · change (2 : Real) ^ (-(31 : Int)) * S.alpha ^ 160 * E.Q.length * R.length * N ≤ _
    calc
      _ = delta * R.length * N * (S.alpha ^ 32 * E.Q.length / 32) := by
        dsimp only [delta]
        rw [show (160 : Nat) = 128 + 32 by omega, pow_add]
        norm_num [zpow_neg]
        ring
      _ ≤ delta * R.length * N * (criticalHeights S D E).card :=
        mul_le_mul_of_nonneg_left hIweak (by dsimp [delta]; positivity)
      _ ≤ _ := hmass

/-- The complete common-step extraction from its Bohr models and numerical
budgets. The conclusion retains `|R| <= |Q|` for the later coefficient step. -/
theorem lemma_13_6_printed_of_bohr_models_with_length {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (theta zeta : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (K : ZMod N → Finset (ZMod N)) (psi : ZMod N → ZMod N → ZMod N)
    (h134 : IsStage134Data S theta D) (h135 : IsStage135Data S D E)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤ (Y h).card)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) ≤
      zeta / m)
    (hmodel : ∀ h ∈ criticalHeights S D E,
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        (K h) zeta (Y h) (psi h)) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  apply lemma_13_6_printed_of_short_difference_rules_with_length S D E h135 m Y hm hsize hupper hlower hY
  intro h hh
  exact corollary_10_14_holds N (Pair N) (section13EdgeIndexDomain N)
    (verticalPhiDifference S.phi h) (K h) zeta (Y h) (psi h) (Fact.out : N.Prime)
    (hmodel h hh) m hm E.Q.step
    (stage136_common_step_mem_bohr S theta zeta D E m K h134 h135 hK hbudget h hh)

/-- Stage 13.6 from the preceding stages and explicit numerical budgets.
All row subsets and Bohr models are constructed; only the density range and
integer/radius inequalities remain as hypotheses. The upper progression
length is preserved for the later coefficient extraction. -/
theorem lemma_13_6_printed_from_initial_stages {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat)
    (hαsixth : S.alpha ≤ 1 / 6)
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
    · obtain ⟨Y, psi, hdata⟩ := section13_printed_uniform_height_model_small_edge S h
        (Finset.mem_filter.mp hh).2
        ((section13_edge_density_bounds S h (Finset.mem_filter.mp hh).2).2.2.trans hαsixth)
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

theorem lemma_13_6_printed_small_row_scale_with_length {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h135 : IsStage135Data S D E)
    (hscale : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ 1) :
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F ∧ F.R.length = 1 := by
  classical
  let delta : Real := (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128
  have hdelta : delta ≤ S.alpha ^ 32 / 16 := by
    have hp : S.alpha ^ 128 ≤ S.alpha ^ 32 := by
      calc
        _ = S.alpha ^ 32 * S.alpha ^ 96 := by rw [← pow_add]
        _ ≤ S.alpha ^ 32 * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one) (by positivity)
        _ = _ := mul_one _
    calc
      _ ≤ (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 32 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (1 / 16 : Real) * S.alpha ^ 32 :=
        mul_le_mul_of_nonneg_right (by norm_num [zpow_neg]) (by positivity)
      _ = _ := by ring
  have hY (h : ZMod N) (hh : h ∈ criticalHeights S D E) :
      delta * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card :=
    (mul_le_mul_of_nonneg_right hdelta (by positivity)).trans
      (section13_strong_height_edge_density S h (Finset.mem_filter.mp hh).2)
  obtain ⟨x, hx⟩ := section13_column_mass_selection S (criticalHeights S D E) delta hY
  let R : ModAP N := ⟨x, E.Q.step, 1⟩
  let F : Stage136Data N := ⟨R, verticalEdgeDomain S.A⟩
  have hR : R.carrier = {x} := by simp [R, ModAP.carrier]
  have hF (h : ZMod N) : stage136RestrictedEdges F h =
      (verticalEdgeDomain S.A h).filter (fun z => z.1 = x) := by
    simp only [stage136RestrictedEdges, F, hR, Finset.mem_singleton]
  have hmass : delta * F.R.length * N * (criticalHeights S D E).card ≤
      ∑ h ∈ criticalHeights S D E, ((stage136RestrictedEdges F h).card : Real) := by
    simpa only [F, R, Nat.cast_one, mul_one, hF, verticalEdgeFiberCount] using hx
  refine ⟨F, ⟨rfl, h135.1, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · change R.carrier.card = 1
    rw [hR, Finset.card_singleton]
  · simpa only [F, R, Nat.cast_one] using hscale
  · intro h hh
    refine ⟨Finset.Subset.refl _, hY h hh, ?_⟩
    rw [hF]
    exact section13_single_column_linear S h x
  · simpa only [Nat.cast_sum] using hmass
  · simp only [Nat.cast_sum]
    have hI : S.alpha ^ 32 * E.Q.length / 32 ≤ (criticalHeights S D E).card := by
      have hc := h135.2.2.2.2.2
      have hn : 0 ≤ S.alpha ^ 32 * (E.Q.length : Real) := by positivity
      linarith only [hc, hn]
    calc
      _ = delta * F.R.length * N * (S.alpha ^ 32 * E.Q.length / 32) := by
        dsimp only [delta]
        rw [show (160 : Nat) = 128 + 32 by omega, pow_add]
        norm_num [zpow_neg]
        ring
      _ ≤ delta * F.R.length * N * (criticalHeights S D E).card :=
        mul_le_mul_of_nonneg_left hI (by dsimp [delta]; positivity)
      _ ≤ _ := hmass

theorem lemma_13_6_printed_improved_length {N : Nat} [NeZero N] (hprime : N.Prime)
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E) (hαsixth : S.alpha ≤ 1 / 6) :
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
    obtain ⟨F, hF, hmR, hRupper⟩ := lemma_13_6_printed_from_initial_stages
      S D E m hαsixth h134 h135 hm hsize hupper (htarget.trans hlower) hbohr
    exact ⟨F, hF, hlower.trans (Nat.cast_le.mpr hmR), hRupper.trans (le_max_right _ _)⟩

/-- Original printed masses and length bound in the explicit small-density
range. The construction in fact supplies the stronger `10Q` length exponent. -/
def lemma_13_6_printed_small_density : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (D : Stage134Data N)
      (E : Stage135Data N),
    Nat.Prime N → S.alpha ≤ 1 / 6 →
    IsStage134Data S ((2 : Real) ^ (-(59 : Int)) * S.alpha ^ 176) D →
    IsStage135Data S D E →
    ∃ F : Stage136Data N, IsStage136DataPrinted S D E F

theorem lemma_13_6_printed_small_density_holds : lemma_13_6_printed_small_density := by
  intro N _ S D E hprime hαsixth h134 h135
  obtain ⟨F, hF, _, _⟩ := lemma_13_6_printed_improved_length hprime S D E
    (by simpa only [section13_lambda_formula S.alpha_pos] using h134) h135 hαsixth
  exact ⟨F, hF⟩

end LeanProofs.GowersSzemeredi
