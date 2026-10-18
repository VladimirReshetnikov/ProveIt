import GowersSzemeredi.Proofs13QuadraticRecurrence
import GowersSzemeredi.Proofs16Slicing

/-! This module keeps `ModAP.interior`, `ModAP.interior_neighbors` and
`stage135AmbientQuadratic`; the rest of the development, with its description,
is in `Proofs13EndpointDeletionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Delete the first and last indexed points of a modular progression. -/
def ModAP.interior {N : Nat} (P : ModAP N) : ModAP N where
  start := P.start + P.step
  step := P.step
  length := P.length - 2

/-- An interior point and both adjacent points belong to the original cell. -/
theorem ModAP.interior_neighbors {N : Nat} (P : ModAP N) {x : ZMod N}
    (hx : x ∈ P.interior.carrier) :
    x ∈ P.carrier ∧ x + P.step ∈ P.carrier ∧ x - P.step ∈ P.carrier := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hi : i.val < P.length - 2 := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨⟨i.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [ModAP.interior]
    push_cast
    ring
  · apply Finset.mem_image.mpr
    refine ⟨⟨i.val + 2, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [ModAP.interior]
    push_cast
    ring
  · apply Finset.mem_image.mpr
    refine ⟨⟨i.val, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [ModAP.interior]
    ring

/-- A quadratic polynomial in the ambient height variable. -/
def stage135AmbientQuadratic {N : Nat} (a b h : ZMod N) : ZMod N :=
  a * (4 : ZMod N)⁻¹ * h ^ 2 + b * (2 : ZMod N)⁻¹ * h

end LeanProofs.GowersSzemeredi
