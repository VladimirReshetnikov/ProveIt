import GowersSzemeredi.Proofs16PackagedExplicitCover
import GowersSzemeredi.Proofs16UnusedCoordinateParameter

/-! Exact companion of the repaired Lemma 16.10. The cross-section
iteration parameter of the structured pair is at least one, so the explicit
sampling and interpolation cover applies on every proper box, at every loss
and at every scale. The refuted printed encoding is untouched. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_16_10_holds : lemma_16_10 := by
  intro N k _ _ hk theta gamma ht ht1 hg hg1 B phi H1 Y x0 hsections hline
    rho hrho hrho1 m P hP hm
  have hs : 1 ≤ gamma ^ (-(2 : Int)) *
      multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k := by
    have h := (section16_face_parameter_lift_reserve k ht ht1 hg hg1).1
    linarith
  exact Section16AllBoxLineCovers.explicit_multilinear_cover hline hsections
    (by omega) hg hg1 hs hrho hrho1 m P hP hm

end LeanProofs.GowersSzemeredi
