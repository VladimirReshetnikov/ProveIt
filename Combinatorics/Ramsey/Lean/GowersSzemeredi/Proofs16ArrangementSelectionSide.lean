import GowersSzemeredi.Proofs16ArrangementSelection

/-! Declarations of `Proofs16ArrangementSelection` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The averaging part of Lemma 16.5, including the exact error parameter
required by Theorem 10.13. Only the arrangement conditions (ii) and (iii) of
Lemma 16.4 are used; the cross-section condition (i) is not. -/
theorem section16_good_sidelengths_of_arrangements {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (htheta : 0 < theta) (hgamma : 0 < gamma)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) ≤
        ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∀ h ∈ H,
        section16ThetaOne theta gamma k / 4 * (N : Real) ^ (16 * k + 15) ≤
          section16ArrangementCountAtSide 8 B h ∧
        DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8 :=
  section16_good_sidelengths_with _ B phi (by unfold section16ThetaOne; positivity) hB

/-- The averaging part of Lemma 16.5 for a structured pair. -/
theorem section16_good_sidelengths {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (htheta : 0 < theta) (hgamma : 0 < gamma)
    (hB : Section16StructuredPair theta gamma B phi) :
    ∃ H : Finset (Point N k),
      section16ThetaOne theta gamma k / 4 * (N : Real) ^ (17 * k + 15) ≤
        ∑ h ∈ H, (section16ArrangementCountAtSide 8 B h : Real) ∧
      ∀ h ∈ H,
        section16ThetaOne theta gamma k / 4 * (N : Real) ^ (16 * k + 15) ≤
          section16ArrangementCountAtSide 8 B h ∧
        DomainApproxHomOfOrder (section16CubeMultifunctionDomain B h)
          (section16InducedCubeMap B h phi) ((2 : Real) ^ (-(43 : Real))) 8 :=
  section16_good_sidelengths_of_arrangements theta gamma B phi htheta hgamma hB.2

end LeanProofs.GowersSzemeredi
