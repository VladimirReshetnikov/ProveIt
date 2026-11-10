import DiophantineConsistency.Sign17ExactDegree
/-! SOURCE-ONLY: MF radix/byte chunk identities; file provenance is external. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MFChunks

theorem first :
    Nat.ofDigits CurrentMasks2011.radix [3, 8, 8, 8, 8, 8, 8, 8] =
      Nat.ofDigits 256 [3, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem eights :
    Nat.ofDigits CurrentMasks2011.radix [8, 8, 8, 8, 8, 8, 8, 8] =
      Nat.ofDigits 256 [8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem end_eights :
    Nat.ofDigits CurrentMasks2011.radix [8, 8, 8, 8, 8, 0, 0, 0] =
      Nat.ofDigits 256 [8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem zeros :
    Nat.ofDigits CurrentMasks2011.radix [0, 0, 0, 0, 0, 0, 0, 0] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem ones :
    Nat.ofDigits CurrentMasks2011.radix [1, 1, 1, 1, 1, 1, 1, 1] =
      Nat.ofDigits 256 [1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem end_ones :
    Nat.ofDigits CurrentMasks2011.radix [1, 0, 0, 0, 0, 0, 0, 0] =
      Nat.ofDigits 256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem start_ones :
    Nat.ofDigits CurrentMasks2011.radix [0, 0, 0, 1, 1, 1, 1, 1] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem end_ones2 :
    Nat.ofDigits CurrentMasks2011.radix [1, 1, 1, 0, 0, 0, 0, 0] =
      Nat.ofDigits 256 [1, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem marker :
    Nat.ofDigits CurrentMasks2011.radix [0, 0, 0, 0, 1, (2 ^ 45 - 4), 0, 0] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 224, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold CurrentMasks2011.radix
  decide +kernel

theorem tail :
    Nat.ofDigits CurrentMasks2011.radix [0, 0, 0, 1] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32] := by
  unfold CurrentMasks2011.radix
  decide +kernel

end DiophantineConsistency.Sign17MFChunks
#print axioms DiophantineConsistency.Sign17MFChunks.first
#print axioms DiophantineConsistency.Sign17MFChunks.eights
#print axioms DiophantineConsistency.Sign17MFChunks.end_eights
#print axioms DiophantineConsistency.Sign17MFChunks.zeros
#print axioms DiophantineConsistency.Sign17MFChunks.ones
#print axioms DiophantineConsistency.Sign17MFChunks.end_ones
#print axioms DiophantineConsistency.Sign17MFChunks.start_ones
#print axioms DiophantineConsistency.Sign17MFChunks.end_ones2
#print axioms DiophantineConsistency.Sign17MFChunks.marker
#print axioms DiophantineConsistency.Sign17MFChunks.tail
