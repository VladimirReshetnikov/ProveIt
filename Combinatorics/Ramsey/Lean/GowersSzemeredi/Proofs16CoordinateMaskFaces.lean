import GowersSzemeredi.Proofs16AmbientFaceCover

/-! Coordinate masks as proper-face retractions. These expose the ambient
cover in the concrete form used by translated cube vertices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A coordinate face with prescribed free coordinate set and fixed anchor. -/
def coordinateSubsetFace {N d : Nat} (s : Finset (Fin d)) (a : Point N d) :
    CoordinateFace N d s.card where
  free := ⟨fun i => ((s.equivFinOfCardEq rfl).symm i).val, by
    intro i j hij
    exact (s.equivFinOfCardEq rfl).symm.injective (Subtype.ext hij)⟩
  anchor := a
  map x j := if h : j ∈ s then x ((s.equivFinOfCardEq rfl) ⟨j, h⟩) else a j
  map_free := by
    intro x i
    simp
  map_fixed := by
    intro x j hj
    have hnot : j ∉ s := by
      intro hmem
      exact hj ((s.equivFinOfCardEq rfl) ⟨j, hmem⟩) (by simp)
    simp [hnot]

@[simp] theorem coordinateSubsetFace_retraction {N d : Nat}
    (s : Finset (Fin d)) (a z : Point N d) (j : Fin d) :
    (coordinateSubsetFace s a).map
      (selectedCoordinates (coordinateSubsetFace s a).free z) j =
      if j ∈ s then z j else a j := by
  classical
  by_cases hj : j ∈ s <;> simp [coordinateSubsetFace, selectedCoordinates, hj]

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
