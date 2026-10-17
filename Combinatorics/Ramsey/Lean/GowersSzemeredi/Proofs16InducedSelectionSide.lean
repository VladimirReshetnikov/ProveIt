import GowersSzemeredi.Proofs16InducedSelection
import GowersSzemeredi.Proofs16Lemma5Side

/-! Declarations of `Proofs16InducedSelection` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Lemma 16.5 together with the induced-value and progression-linearity
input subsequently used in Lemmas 16.6 and 16.7. -/
theorem section16_models_and_induced_selection {N k : Nat} [NeZero N]
    (hprime : N.Prime) (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hB : Section16StructuredPair theta gamma B phi) :
    ∃ H : Finset (Point N k),
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ psi phiPrime : Point N k → ZMod N → ZMod N,
          section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) ≤
            ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
          (∀ h ∈ H,
            (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
              (section16CubeDomain B h).card ≤ (Y h).card ∧
            HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
              (section16InducedCubeMap B h phi)
              (section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
              (section16Zeta theta gamma k) (Y h) (psi h)) ∧
          Section16InducedSelection B phi H Y
            (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
            (section16Zeta theta gamma k) phiPrime := by
  obtain ⟨H, hmass, Y, psi, hmodel⟩ := lemma_16_5_holds N k theta gamma B phi ht ht1 hg hg1 hB
  obtain ⟨phiPrime, hselection⟩ := section16_inducedSelection_exists B phi H Y _ _ psi hprime
    (by unfold section16Zeta; positivity) (fun h hh => (hmodel h hh).2)
  exact ⟨H, Y, psi, phiPrime, hmass, hmodel, hselection⟩

end LeanProofs.GowersSzemeredi
