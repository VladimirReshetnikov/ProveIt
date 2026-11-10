import DiophantineConsistency.Sign14PrefixDagShared04

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared25Bytes : List Char := ('+' :: (shared19Bytes ++ shared14Bytes))
theorem shared25Bytes_eq : shared25Bytes = encode Sign14PrefixCode.shared25 := by
  unfold shared25Bytes
  simp only [shared19Bytes_eq, shared14Bytes_eq] <;> rfl

def shared26Bytes : List Char := ('+' :: (shared24Bytes ++ fragment020))
theorem shared26Bytes_eq : shared26Bytes = encode Sign14PrefixCode.shared26 := by
  unfold shared26Bytes
  simp only [shared24Bytes_eq, fragment020_eq] <;> rfl

def shared27Bytes : List Char := ('+' :: (shared22Bytes ++ shared09Bytes))
theorem shared27Bytes_eq : shared27Bytes = encode Sign14PrefixCode.shared27 := by
  unfold shared27Bytes
  simp only [shared22Bytes_eq, shared09Bytes_eq] <;> rfl

def shared28Bytes : List Char := ('*' :: (fragment021 ++ shared26Bytes))
theorem shared28Bytes_eq : shared28Bytes = encode Sign14PrefixCode.shared28 := by
  unfold shared28Bytes
  simp only [fragment021_eq, shared26Bytes_eq] <;> rfl

def shared29Bytes : List Char := ('*' :: (shared18Bytes ++ shared16Bytes))
theorem shared29Bytes_eq : shared29Bytes = encode Sign14PrefixCode.shared29 := by
  unfold shared29Bytes
  simp only [shared18Bytes_eq, shared16Bytes_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared25Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared26Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared27Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared28Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared29Bytes_eq
