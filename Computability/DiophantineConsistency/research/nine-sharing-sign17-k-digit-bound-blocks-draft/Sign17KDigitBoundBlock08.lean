import DiophantineConsistency.Sign17KRadixStreamCurrent

/-! SOURCE ONLY. One finite literal coefficient block bound. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KDigitBoundBlock08

theorem bound (i : Fin 64) :
    Sign17KTileCoefficients08.literal i + 1 < CurrentKernel2011.radix := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KDigitBoundBlock08
#print axioms DiophantineConsistency.Sign17KDigitBoundBlock08.bound
