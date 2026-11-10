import DiophantineConsistency.Sign17KStreamExplicit
import DiophantineConsistency.Sign17KByteCompose

/-! SOURCE ONLY. One bounded comparison of actual and fixture radix digits. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KStreamCompare00

theorem chunk :
    ((Sign17KRadixStream.lowPrefix ++
      (Sign17KStreamExplicit.coefficientsReversed.set 984 30099357829123 ++
        Sign17KRadixStream.suffix)).drop 0).take 256 =
    (Sign17KByteCompose.digitList.drop 0).take 256 := by
  decide +kernel

end DiophantineConsistency.Sign17KStreamCompare00
#print axioms DiophantineConsistency.Sign17KStreamCompare00.chunk
