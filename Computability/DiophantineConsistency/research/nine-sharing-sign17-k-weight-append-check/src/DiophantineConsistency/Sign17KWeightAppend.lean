import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: generic composition of adjacent finite weight certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightAppend

theorem append_certificates {α β : Type} {m n : ℕ} (f : α → β)
    (leftIndex : Fin m → α) (rightIndex : Fin n → α)
    (leftValue : Fin m → β) (rightValue : Fin n → β)
    (hleft : ∀ i, f (leftIndex i) = leftValue i)
    (hright : ∀ i, f (rightIndex i) = rightValue i) :
    ∀ i, f ((Fin.append leftIndex rightIndex) i) =
      (Fin.append leftValue rightValue) i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left] using hleft j
  · intro j
    simpa only [Fin.append_right] using hright j

end DiophantineConsistency.Sign17KWeightAppend
#print axioms DiophantineConsistency.Sign17KWeightAppend.append_certificates
