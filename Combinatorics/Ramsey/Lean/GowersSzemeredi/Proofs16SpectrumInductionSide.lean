import GowersSzemeredi.Proofs16SpectrumInduction
import GowersSzemeredi.Proofs16Lemma6Parameters

/-! Declarations of `Proofs16SpectrumInduction` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Apply the lower-dimensional induction to the spectrum with a threshold
independent of B. These are exactly the parameters entering Lemma 16.6. -/
theorem Theorem162At.restrict_spectrum {k : Nat} (hth : Theorem162At k)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ B : Finset (Point N (k + 1)), ∃ J : Finset (Point N k),
        (1 - section16ThetaOne theta gamma k / 8) * (N : Real) ^ k ≤ J.card ∧
        MultiplyLinear (section16Delta (section16ThetaOne theta gamma k))
          (section16T (section16Delta (section16ThetaOne theta gamma k))
            (section16ThetaOne theta gamma k) k)
          (restrictRelation (section16SpectrumRelation B (section16Delta (section16ThetaOne theta gamma k))) J) := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := hth _ _ hd hd1 (by positivity : 0 < section16ThetaOne theta gamma k / 8)
    (by linarith : section16ThetaOne theta gamma k / 8 ≤ 1)
  refine ⟨N0, fun N _ _ hN B => ?_⟩
  exact hN0 N hN _ (section16_spectrum_relation_card B hd) (section16_spectrum_relation_product B hd)

end LeanProofs.GowersSzemeredi
