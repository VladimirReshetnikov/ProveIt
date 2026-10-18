import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs16RadiusComparison

/-! Declarations of `Proofs16Lemma5` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- **Lemma 16.5 with parameters**: from the arrangement conditions at density
`t1`, many sidelengths carry a Bohr difference model at radius `zeta`. -/
theorem lemma_16_5_with {N k : Nat} [NeZero N] (t1 zeta : Real)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤ generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      t1 / 4 * (N : Real) ^ (17 * k + 15) ≤
          ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ psi : Point N k → ZMod N → ZMod N,
          ∀ h, h ∈ H →
            (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 *
                (section16CubeDomain B h).card ≤ (Y h).card ∧
            HasBohrDifferenceModel
              (section16CubeMultifunctionDomain B h)
              (section16InducedCubeMap B h phi)
              (section16LargeSpectrum B h (section16Delta t1)) zeta (Y h) (psi h) := by
  have ht1 : 0 ≤ t1 := by linarith
  obtain ⟨H, hmass, hgood⟩ := section16_good_sidelengths_with t1 B phi ht1 hB
  refine ⟨H, hmass, ?_⟩
  have hex : ∀ h : Point N k,
      ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
        h ∈ H →
        (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 * (section16CubeDomain B h).card ≤ Y.card ∧
        HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) (section16LargeSpectrum B h (section16Delta t1))
          zeta Y psi := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨Y, psi, hY⟩ := section16_selected_side_model_with t1 zeta B phi h ha0 haS hzeta
        (hgood h hh).1 (hgood h hh).2
      exact ⟨Y, psi, fun _ => hY⟩
    · exact ⟨∅, fun _ => 0, fun hmem => (hh hmem).elim⟩
  choose Y psi hY using hex
  exact ⟨Y, psi, hY⟩

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The printed parameters satisfy the hypotheses: `lemma_16_5_with` contains
the printed Lemma 16.5's conclusion. -/
theorem lemma_16_5_with_printed_hyps {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k / 4 ∧ section16ThetaOne theta gamma k / 4 ≤ 1 / 36 ∧
      ∀ alpha : Real, section16ThetaOne theta gamma k / 4 ≤ alpha → alpha ≤ 1 / 6 →
        section16Zeta theta gamma k ≤ section10Zeta alpha := by
  obtain ⟨h0, h1⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  exact ⟨h0, h1, fun alpha ha ha1 => section16_zeta_le_section10Zeta k ht ht1 hg hg1 ha ha1⟩

/-- Exact companion for Lemma 16.5. -/
theorem lemma_16_5_holds : lemma_16_5 := by
  intro N k _ theta gamma B phi ht ht1 hg hg1 hB
  have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1
  exact lemma_16_5_with _ _ B phi hp.1 hp.2.1 hp.2.2 hB.2

end LeanProofs.GowersSzemeredi
