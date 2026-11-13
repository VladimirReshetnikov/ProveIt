import DiophantineConsistency.Sign14PrefixDagShared02

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared15Bytes : List Char := ('*' :: (shared03Bytes ++ shared12Bytes))
theorem shared15Bytes_eq : shared15Bytes = encode Sign14PrefixCode.shared15 := by
  unfold shared15Bytes
  simp only [shared03Bytes_eq, shared12Bytes_eq] <;> rfl

def shared16Bytes : List Char := ('*' :: (fragment015 ++ shared13Bytes))
theorem shared16Bytes_eq : shared16Bytes = encode Sign14PrefixCode.shared16 := by
  unfold shared16Bytes
  simp only [fragment015_eq, shared13Bytes_eq] <;> rfl

def shared17Bytes : List Char := ('+' :: (shared16Bytes ++ fragment016))
theorem shared17Bytes_eq : shared17Bytes = encode Sign14PrefixCode.shared17 := by
  unfold shared17Bytes
  simp only [shared16Bytes_eq, fragment016_eq] <;> rfl

def shared18Bytes : List Char := ('*' :: (shared05Bytes ++ shared13Bytes))
theorem shared18Bytes_eq : shared18Bytes = encode Sign14PrefixCode.shared18 := by
  unfold shared18Bytes
  simp only [shared05Bytes_eq, shared13Bytes_eq] <;> rfl

def shared19Bytes : List Char := ('*' :: (shared17Bytes ++ fragment017))
theorem shared19Bytes_eq : shared19Bytes = encode Sign14PrefixCode.shared19 := by
  unfold shared19Bytes
  simp only [shared17Bytes_eq, fragment017_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared15Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared16Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared17Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared18Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared19Bytes_eq
