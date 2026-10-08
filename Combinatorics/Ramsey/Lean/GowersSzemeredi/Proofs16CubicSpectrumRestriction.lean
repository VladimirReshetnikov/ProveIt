import GowersSzemeredi.Proofs16BaseCaseCubicExtraction
import GowersSzemeredi.Proofs16SpectrumInduction

/-! The spectrum in dimension two has loss-independent graph controls.
Apply the strengthened one-dimensional extraction directly to the proved
size and product-property bounds for the spectrum relation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16CubicSpectrumCount (theta gamma : Real) : Nat :=
  section16BaseFamilyBound (section16Delta (section16ThetaOne theta gamma 1))
    (section16ThetaOne theta gamma 1 / 8)

theorem section16CubicSpectrumCount_pos (theta gamma : Real) :
    0 < section16CubicSpectrumCount theta gamma := section16BaseFamilyBound_pos _ _

/-- The one-dimensional large-spectrum relation admits a restriction with
constant graph count and a cubic exponent in the later requested loss. -/
theorem section16_cubic_spectrum_restriction {N : Nat} [Fact N.Prime]
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (B : Finset (Point N 2)) :
    ∃ J : Finset (Point N 1),
      (1 - section16ThetaOne theta gamma 1 / 8) * (N : Real) ≤ J.card ∧
      MultiplyLinearWith
        (fun _ => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real))
        (cubicBaseExponent (section16CubicSpectrumCount theta gamma))
        (restrictRelation (section16SpectrumRelation B
          (section16Delta (section16ThetaOne theta gamma 1))) J) := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 1 ht ht1 hg hg1
  exact section16_product_relation_cubic_cover hd hd1 (by positivity) (by linarith)
    (section16SpectrumRelation B (section16Delta (section16ThetaOne theta gamma 1)))
    (by simpa using section16_spectrum_relation_card B hd)
    (section16_spectrum_relation_product B hd)

end LeanProofs.GowersSzemeredi
