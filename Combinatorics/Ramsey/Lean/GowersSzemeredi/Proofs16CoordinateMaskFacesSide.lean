import GowersSzemeredi.Proofs16CoordinateMaskFaces
import GowersSzemeredi.Proofs16AmbientFaceCover

/-! Declarations of `Proofs16CoordinateMaskFaces` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Every strict coordinate mask inherits an ambient cover from the proper
cross-sections, with the same iteration parameter. -/
theorem ProperCrossSectionsMultiplyLinear.coordinate_mask_cover
    {N d : Nat} [NeZero N] [Fact N.Prime] {gamma r : Real}
    {B : Finset (Point N d)} {phi : Point N d → ZMod N}
    (hfaces : ProperCrossSectionsMultiplyLinear gamma r B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 2 ≤ r)
    (hgraphs : ((3 ^ d : Nat) : Real) ≤ r)
    (s : Finset (Fin d)) (hs : s.card < d) (a t : Point N d)
    (D : Finset (Point N d))
    (hD : ∀ z ∈ D, (fun j => if j ∈ s then (z + t) j else a j) ∈ B) :
    MultiplyLinearFunction gamma r D
      (fun z => phi (fun j => if j ∈ s then (z + t) j else a j)) := by
  have heq : ∀ z, (coordinateSubsetFace s a).map
      (selectedCoordinates (coordinateSubsetFace s a).free (z + t)) =
      (fun j => if j ∈ s then (z + t) j else a j) := by
    intro z
    funext j
    exact coordinateSubsetFace_retraction s a (z + t) j
  have hp := hfaces.ambient_face_cover hg hg1 hr hgraphs
    (coordinateSubsetFace s a) hs t D (by simpa only [heq] using hD)
  simpa only [heq] using hp

end LeanProofs.GowersSzemeredi
