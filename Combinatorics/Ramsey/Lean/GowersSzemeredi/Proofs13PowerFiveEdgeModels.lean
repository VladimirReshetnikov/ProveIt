import GowersSzemeredi.Proofs13UniformEdgeModels

/-! Propagate the stronger five-power Theorem 10.13 extraction to the
vertical-edge domains of Section 13. Spectrum cutoffs and Bohr radii remain
unchanged. The original printed stronger extraction remains separate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Apply Theorem 10.13 to a good height at its actual normalized edge
density. The selected set is transported back to lower-endpoint pairs without
losing cardinality or changing the Fourier spectrum and Bohr radius. -/
theorem section13_good_height_bohr_model_power_five {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsGoodHeight S h) (beta : Real)
    (hβ : 0 < beta) (hβsixth : beta ≤ 1 / 6)
    (hcard : ((verticalEdgeDomain S.A h).card : Real) = beta * (N : Real) ^ 2) :
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      beta ^ 5 * (verticalEdgeDomain S.A h).card / 20000 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  classical
  have hcard' : (Fintype.card (Section13Edges S.A h) : Real) = beta * N * N := by
    rw [Fintype.card_coe, hcard]
    ring
  have hmain := theorem_10_13_power_five_holds N N (Section13Edges S.A h)
    (section13VerticalDomain S.A h) (fun z ↦ verticalPhiDifference S.phi h z.val) beta
    hβ hβsixth (NeZero.pos N) (section13_vertical_fibre_cap S.A h) hcard'
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

/-- Strong-height Bohr models with the corrected Stage 13.6 set-size bound.
The density range used by the checked Theorem 10.13 remains explicit, and
the spectrum and radius use the actual edge density. -/
theorem section13_strong_height_bohr_model_power_five {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hαsixth : S.alpha ≤ 1 / 6) :
    let beta := section13EdgeDensity S h
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(39 : Int)) * S.alpha ^ 192 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  have hbounds := section13_edge_density_bounds S h hh
  obtain ⟨Y, psi, hsub, hmass, hmodel⟩ := section13_good_height_bohr_model_power_five S h hh.2
    (section13EdgeDensity S h) hbounds.1 (hbounds.2.2.trans hαsixth)
    (section13_edge_density_card S h)
  refine ⟨Y, psi, hsub, ?_, hmodel⟩
  let a : Real := S.alpha ^ 32 / 16
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow : a ^ 5 ≤ section13EdgeDensity S h ^ 5 :=
    pow_le_pow_left₀ ha hbounds.2.1 5
  have hedge : a * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card :=
    section13_strong_height_edge_density S h hh
  have hβ : 0 < section13EdgeDensity S h := hbounds.1
  have hproduct : a ^ 5 * (a * (N : Real) ^ 2) ≤
      section13EdgeDensity S h ^ 5 * (verticalEdgeDomain S.A h).card :=
    mul_le_mul hpow hedge (by positivity) (by positivity)
  have hpower : a ^ 5 * a = S.alpha ^ 192 / (2 : Real) ^ 24 := by
    dsimp only [a]
    ring
  calc
    _ ≤ (S.alpha ^ 192 / (2 : Real) ^ 24) * (N : Real) ^ 2 / 20000 := by
      norm_num [zpow_neg]
      have hnonneg : 0 ≤ S.alpha ^ 192 * (N : Real) ^ 2 :=
        mul_nonneg (pow_nonneg S.alpha_pos.le 192) (sq_nonneg _)
      nlinarith only [hnonneg]
    _ = a ^ 5 * (a * (N : Real) ^ 2) / 20000 := by rw [← hpower]; ring
    _ ≤ section13EdgeDensity S h ^ 5 * (verticalEdgeDomain S.A h).card / 20000 :=
      div_le_div_of_nonneg_right hproduct (by norm_num)
    _ ≤ Y.card := hmass

/-- All strong heights have models at the same lower-density threshold and
radius, retaining the corrected set-size bound. -/
theorem section13_uniform_height_bohr_model_power_five {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hαsixth : S.alpha ≤ 1 / 6) :
    let a := S.alpha ^ 32 / 16
    let K := domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(39 : Int)) * S.alpha ^ 192 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta a) Y psi := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  have ha : 0 < a := by dsimp [a]; have := S.alpha_pos; positivity
  have hbounds := section13_edge_density_bounds S h hh
  have hβone : section13EdgeDensity S h ≤ 1 := hbounds.2.2.trans S.alpha_at_most_one
  have hzeta := section10Zeta_mono ha hbounds.2.1 hβone
  have hlam : section10Lambda a ≤ section10Lambda (section13EdgeDensity S h) := by
    unfold section10Lambda
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ha.le hbounds.2.1 (by norm_num)) (by positivity)
  obtain ⟨Y, psi, hY, hmass, hmodel⟩ := section13_strong_height_bohr_model_power_five S h hh hαsixth
  refine ⟨Y, psi, hY, hmass, ?_⟩
  apply bohr_difference_model_restrict _ _ _ _ _ _ _ _ hmodel
  apply bohr_domain_mono ?_ hzeta
  intro r hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans
      (Finset.mem_filter.mp hr).2

end LeanProofs.GowersSzemeredi
