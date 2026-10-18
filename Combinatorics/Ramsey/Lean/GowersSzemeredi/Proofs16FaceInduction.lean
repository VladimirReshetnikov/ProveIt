import GowersSzemeredi.Proofs16CoordinateFaces

/-! This module keeps `partialGraph_card` and `restrictRelation_partialGraph`; the
rest of the development, with its description, is in
`Proofs16FaceInductionSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem partialGraph_card {N l : Nat} (B : Finset (Point N l))
    (phi : Point N l → ZMod N) : (partialGraph B phi).card = B.card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem restrictRelation_partialGraph {N l : Nat} (B J : Finset (Point N l))
    (phi : Point N l → ZMod N) :
    restrictRelation (partialGraph B phi) J = partialGraph (B ∩ J) phi := by
  ext ⟨x, y⟩
  simp [restrictRelation, partialGraph, and_assoc, and_comm]

end LeanProofs.GowersSzemeredi
