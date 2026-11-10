import DiophantineConsistency.Sign14PrefixDagShared05

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared30Bytes : List Char := ('+' :: (shared21Bytes ++ shared14Bytes))
theorem shared30Bytes_eq : shared30Bytes = encode Sign14PrefixCode.shared30 := by
  unfold shared30Bytes
  simp only [shared21Bytes_eq, shared14Bytes_eq] <;> rfl

def shared31Bytes : List Char := ('*' :: (shared23Bytes ++ shared17Bytes))
theorem shared31Bytes_eq : shared31Bytes = encode Sign14PrefixCode.shared31 := by
  unfold shared31Bytes
  simp only [shared23Bytes_eq, shared17Bytes_eq] <;> rfl

def shared32Bytes : List Char := ('+' :: (shared07Bytes ++ shared31Bytes))
theorem shared32Bytes_eq : shared32Bytes = encode Sign14PrefixCode.shared32 := by
  unfold shared32Bytes
  simp only [shared07Bytes_eq, shared31Bytes_eq] <;> rfl

def shared33Bytes : List Char := ('*' :: (shared23Bytes ++ shared23Bytes))
theorem shared33Bytes_eq : shared33Bytes = encode Sign14PrefixCode.shared33 := by
  unfold shared33Bytes
  simp only [shared23Bytes_eq] <;> rfl

def shared34Bytes : List Char := ('-' :: (shared25Bytes ++ shared27Bytes))
theorem shared34Bytes_eq : shared34Bytes = encode Sign14PrefixCode.shared34 := by
  unfold shared34Bytes
  simp only [shared25Bytes_eq, shared27Bytes_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared30Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared31Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared32Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared33Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared34Bytes_eq
