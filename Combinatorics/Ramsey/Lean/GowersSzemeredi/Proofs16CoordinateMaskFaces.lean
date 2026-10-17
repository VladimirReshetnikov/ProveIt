import GowersSzemeredi.Proofs16EmbeddedLift

/-! Coordinate masks as proper-face retractions. These expose the ambient
cover in the concrete form used by translated cube vertices.

`ProperCrossSectionsMultiplyLinear.coordinate_mask_cover` is in
`Proofs16CoordinateMaskFacesSide`, outside the final route. -/
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
  by_cases hj : j ∈ s <;> simp [coordinateSubsetFace, selectedCoordinates, hj]

end LeanProofs.GowersSzemeredi
