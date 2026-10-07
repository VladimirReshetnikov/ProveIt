import GowersSzemeredi.Proofs13UniformEdgeModels

/-! Adaptive fibre normalization removes the ambient density restriction
from the Section 13 Bohr models without changing their quantitative output. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The good-height model with any valid fibre cap, rather than just N. -/
theorem section13_good_height_model_with_cap {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsGoodHeight S h)
    (M : Nat) (hNM : N ≤ M) (beta : Real)
    (hβ : 0 < beta) (hβsixth : beta ≤ 1 / 6)
    (hcard : ((verticalEdgeDomain S.A h).card : Real) = beta * M * N) :
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * M * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      beta ^ 6 * (verticalEdgeDomain S.A h).card / 20000 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  classical
  have hcard' : (Fintype.card (Section13Edges S.A h) : Real) = beta * M * N := by
    simpa only [Fintype.card_coe] using hcard
  have hmain := theorem_10_13_holds N M (Section13Edges S.A h)
    (section13VerticalDomain S.A h) (fun z ↦ verticalPhiDifference S.phi h z.val) beta
    hβ hβsixth ((NeZero.pos N).trans_le hNM)
    (fun s => (section13_vertical_fibre_cap S.A h s).trans hNM) hcard'
    (section13_good_height_approx S h hh)
  obtain ⟨Y, psi, hY, hmodel⟩ := hmain.2.2
  let e : Section13Edges S.A h ↪ Pair N := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨Y.map e, psi, ?_, ?_, hmodel.1, ?_⟩
  · intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
    exact v.property
  · simpa only [Finset.card_map, Fintype.card_coe] using hY
  · intro z hz w hw hzw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    exact hmodel.2 v hv u hu hzw

/-- Above density 1/6, the adaptive integer cap keeps the normalized density
between 1/12 and 1/6. -/
theorem section13_dense_normalization {beta : Real} (hβ : 1 / 6 < beta) :
    let k := Nat.ceil (6 * beta)
    0 < k ∧ (1 : Real) / 12 ≤ beta / k ∧ beta / k ≤ 1 / 6 := by
  dsimp only
  have hβpos : 0 < beta := by linarith only [hβ]
  have hk : 0 < Nat.ceil (6 * beta) := Nat.ceil_pos.mpr (by positivity)
  have hkreal : (0 : Real) < Nat.ceil (6 * beta) := by exact_mod_cast hk
  have hlower := Nat.le_ceil (6 * beta)
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ 6 * beta by positivity)
  refine ⟨hk, (le_div_iff₀ hkreal).mpr ?_, (div_le_iff₀ hkreal).mpr ?_⟩ <;>
    linarith only [hβ, hlower, hupper]

/-- The small-edge-density case only needs the edge density at most 1/6;
the original context may have any density at most one. -/
theorem section13_small_edge_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hβsixth : section13EdgeDensity S h ≤ 1 / 6) :
    let beta := section13EdgeDensity S h
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  have hbounds := section13_edge_density_bounds S h hh
  obtain ⟨Y, psi, hsub, hmass, hmodel⟩ := section13_good_height_bohr_model S h hh.2
    (section13EdgeDensity S h) hbounds.1 hβsixth (section13_edge_density_card S h)
  refine ⟨Y, psi, hsub, ?_, hmodel⟩
  let a : Real := S.alpha ^ 32 / 16
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow : a ^ 6 ≤ section13EdgeDensity S h ^ 6 := pow_le_pow_left₀ ha hbounds.2.1 6
  have hedge : a * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card :=
    section13_strong_height_edge_density S h hh
  have hproduct : a ^ 6 * (a * (N : Real) ^ 2) ≤
      section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card :=
    mul_le_mul hpow hedge (by positivity) (by positivity)
  have hpower : a ^ 6 * a = S.alpha ^ 224 / (2 : Real) ^ 28 := by dsimp [a]; ring
  calc
    _ ≤ (S.alpha ^ 224 / (2 : Real) ^ 28) * (N : Real) ^ 2 / 20000 := by
      norm_num [zpow_neg]
      have hnonneg := mul_nonneg (pow_nonneg S.alpha_pos.le 224) (sq_nonneg (N : Real))
      nlinarith only [hnonneg]
    _ = a ^ 6 * (a * (N : Real) ^ 2) / 20000 := by rw [← hpower]; ring
    _ ≤ section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card / 20000 :=
      div_le_div_of_nonneg_right hproduct (by norm_num)
    _ ≤ Y.card := hmass

/-- Uniform strong-height Bohr models for every ambient density at most one.
The spectrum, radius, and selected mass are unchanged from the small-density
construction. -/
theorem section13_uniform_height_model_all_densities {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) :
    let a := S.alpha ^ 32 / 16
    let K := domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
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
  · obtain ⟨Y, psi, hY, hmass, hmodel⟩ := section13_small_edge_model S h hh hsmall
    refine ⟨Y, psi, hY, hmass, ?_⟩
    apply bohr_difference_model_restrict _ _ _ _ _ _ _ _ hmodel
    apply bohr_domain_mono ?_ (section10Zeta_mono ha hbounds.2.1 hβone)
    intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hlam : section10Lambda a ≤ section10Lambda beta := by
      unfold section10Lambda
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hbounds.2.1 (by norm_num)) (by positivity)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg N)) (Nat.cast_nonneg N)).trans
        (Finset.mem_filter.mp hr).2
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
      have hαpow := pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one (n := 224)
      have hcoeff : (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 ≤ b ^ 6 * beta / 20000 := by
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

end LeanProofs.GowersSzemeredi
