import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: verify a three-block Fin.addCases partition pattern. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KPartitionProbe

theorem split_three (P : Fin 9 → Prop)
    (h0 : ∀ i : Fin 2, P (i.castAdd 7))
    (h1 : ∀ i : Fin 3, P ((Fin.natAdd 2 i).castAdd 4))
    (h2 : ∀ i : Fin 4, P (Fin.natAdd 5 i)) : ∀ i, P i := by
  intro i
  refine Fin.addCases (m := 2) (n := 7) ?_ ?_ i
  · intro j
    exact h0 j
  · intro j
    refine Fin.addCases (m := 3) (n := 4) ?_ ?_ j
    · intro k
      simpa [Fin.natAdd, Fin.castAdd, Nat.add_assoc] using h1 k
    · intro k
      simpa [Fin.natAdd, Nat.add_assoc] using h2 k

end DiophantineConsistency.Sign17KPartitionProbe
#print axioms DiophantineConsistency.Sign17KPartitionProbe.split_three
