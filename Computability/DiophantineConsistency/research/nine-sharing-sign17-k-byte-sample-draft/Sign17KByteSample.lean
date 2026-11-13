import DiophantineConsistency.Sign17KRadixStreamCurrent

/-! SOURCE ONLY. Selected radix/byte fixture identities; source file provenance is external. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KByteSample

theorem block002 :
    Nat.ofDigits CurrentKernel2011.radix [0, 0, 1, 0, 262144, 131072, 65536, 32768] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

theorem block125 :
    Nat.ofDigits CurrentKernel2011.radix [30031177328642, 30099130812418, 30099131336706, 30099357304834, 30099357829123, 69752854530, 0, 0] =
      Nat.ofDigits 256 [2, 40, 168, 45, 80, 27, 1, 4, 0, 0, 176, 141, 0, 2, 2, 0, 216, 70, 0, 1, 176, 1, 108, 51, 128, 128, 216, 0, 182, 17, 192, 192, 236, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem block126 :
    Nat.ofDigits CurrentKernel2011.radix [0, 0, 0, 0, 0, 0, 0, 0] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem block252 :
    Nat.ofDigits CurrentKernel2011.radix [0, 0, 0, 0, 1] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16] := by
  decide +kernel
end DiophantineConsistency.Sign17KByteSample
#print axioms DiophantineConsistency.Sign17KByteSample.block002
#print axioms DiophantineConsistency.Sign17KByteSample.block125
#print axioms DiophantineConsistency.Sign17KByteSample.block126
#print axioms DiophantineConsistency.Sign17KByteSample.block252
