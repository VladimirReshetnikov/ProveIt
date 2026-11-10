import DiophantineConsistency.Sign17ExactDegree
/-! SOURCE-ONLY: six MC radix/byte block identities; file binding is external. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCChunks

theorem all_selected :
    Nat.ofDigits CurrentMasks2011.radix [CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2] =
      Nat.ofDigits 256 [254, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 191, 255, 255, 255, 255, 255, 223, 255, 255, 255, 255, 255, 239, 255, 255, 255, 255, 255, 247, 255, 255, 255, 255, 255, 251, 255, 255, 255, 255, 255, 253, 255, 255, 255, 255, 255] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem boundary_951 :
    Nat.ofDigits CurrentMasks2011.radix [CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 1] =
      Nat.ofDigits 256 [254, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 191, 255, 255, 255, 255, 255, 223, 255, 255, 255, 255, 255, 239, 255, 255, 255, 255, 255, 247, 255, 255, 255, 255, 255, 251, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem all_unselected :
    Nat.ofDigits CurrentMasks2011.radix [CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1] =
      Nat.ofDigits 256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem boundary_986 :
    Nat.ofDigits CurrentMasks2011.radix [CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1] =
      Nat.ofDigits 256 [254, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem marker_1004 :
    Nat.ofDigits CurrentMasks2011.radix [CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 2, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1] =
      Nat.ofDigits 256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 239, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem final_3 :
    Nat.ofDigits CurrentMasks2011.radix [CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1, CurrentMasks2011.radix - 1] =
      Nat.ofDigits 256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 31] := by
  unfold CurrentMasks2011.radix
  decide +kernel

end DiophantineConsistency.Sign17MCChunks
#print axioms DiophantineConsistency.Sign17MCChunks.all_selected
#print axioms DiophantineConsistency.Sign17MCChunks.boundary_951
#print axioms DiophantineConsistency.Sign17MCChunks.all_unselected
#print axioms DiophantineConsistency.Sign17MCChunks.boundary_986
#print axioms DiophantineConsistency.Sign17MCChunks.marker_1004
#print axioms DiophantineConsistency.Sign17MCChunks.final_3
