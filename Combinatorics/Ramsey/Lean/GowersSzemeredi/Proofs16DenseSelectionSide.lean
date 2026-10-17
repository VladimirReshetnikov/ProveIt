import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16Lemma5Side

/-! Declarations of `Proofs16DenseSelection` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- One family of actual Bohr-model selections simultaneously retains the
sidelength density, every cube-domain density, and the induced map. Only the
arrangement conditions (ii) and (iii) of Lemma 16.4 are used. -/
theorem section16_dense_induced_selection_of_arrangements {N k : Nat} [NeZero N]
    (hprime : N.Prime) (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ phiPrime : Point N k → ZMod N → ZMod N,
          section16ThetaOne theta gamma k / 4 * (N : Real) ^ k ≤ H.card ∧
          (∀ h ∈ H, section16ThetaOne theta gamma k / 4 * (N : Real) ^ (k + 1) ≤
            (section16CubeDomain B h).card) ∧
          (∀ h ∈ H, (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
            (section16CubeDomain B h).card ≤ (Y h).card) ∧
          Section16InducedSelection B phi H Y
            (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
            (section16Zeta theta gamma k) phiPrime :=
  have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1
  section16_dense_induced_selection_with hprime _ _ B phi hp.1 hp.2.1 hp.2.2
    (by unfold section16Zeta; positivity) hB

/-- One family of actual Bohr-model selections for a structured pair. -/
theorem section16_dense_induced_selection {N k : Nat} [NeZero N]
    (hprime : N.Prime) (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hB : Section16StructuredPair theta gamma B phi) :
    ∃ H : Finset (Point N k),
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ phiPrime : Point N k → ZMod N → ZMod N,
          section16ThetaOne theta gamma k / 4 * (N : Real) ^ k ≤ H.card ∧
          (∀ h ∈ H, section16ThetaOne theta gamma k / 4 * (N : Real) ^ (k + 1) ≤
            (section16CubeDomain B h).card) ∧
          (∀ h ∈ H, (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
            (section16CubeDomain B h).card ≤ (Y h).card) ∧
          Section16InducedSelection B phi H Y
            (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
            (section16Zeta theta gamma k) phiPrime :=
  section16_dense_induced_selection_of_arrangements hprime theta gamma B phi ht ht1 hg hg1 hB.2

end LeanProofs.GowersSzemeredi
