import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs18LengthSixCounts

/-! This module keeps `HasProductProperty.final_section`; the rest of the
development, with its description, is in `Proofs16ThreeSlicesSide`, outside the
final route. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- A final-coordinate section inherits the product property, in every dimension. -/
theorem HasProductProperty.final_section {N k : Nat} [NeZero N] {gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hprod : HasProductProperty B phi gamma) (t : ZMod N) :
    HasProductProperty (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) gamma := by
  have h := hprod.coordinateFace (lastSliceFace k t)
  have hdom : (lastSliceFace k t).domain B = section16FinalCoordinateSection B t := by
    ext x
    simp [CoordinateFace.domain, section16FinalCoordinateSection, lastSliceFace]
  have hfun : (lastSliceFace k t).pullback phi = section16FinalCoordinateRestriction phi t := by
    funext x
    rfl
  rw [hdom, hfun] at h
  exact h

end LeanProofs.GowersSzemeredi
