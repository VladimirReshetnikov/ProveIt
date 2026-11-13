import DiophantineConsistency.Sign14PrefixDagShared07

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared40Bytes : List Char := ('+' :: (shared33Bytes ++ shared26Bytes))
theorem shared40Bytes_eq : shared40Bytes = encode Sign14PrefixCode.shared40 := by
  unfold shared40Bytes
  simp only [shared33Bytes_eq, shared26Bytes_eq] <;> rfl

def shared41Bytes : List Char := ('*' :: (shared38Bytes ++ shared39Bytes))
theorem shared41Bytes_eq : shared41Bytes = encode Sign14PrefixCode.shared41 := by
  unfold shared41Bytes
  simp only [shared38Bytes_eq, shared39Bytes_eq] <;> rfl

def shared42Bytes : List Char := ('*' :: (fragment024 ++ shared41Bytes))
theorem shared42Bytes_eq : shared42Bytes = encode Sign14PrefixCode.shared42 := by
  unfold shared42Bytes
  simp only [fragment024_eq, shared41Bytes_eq] <;> rfl

def shared43Bytes : List Char := ('*' :: (shared42Bytes ++ shared42Bytes))
theorem shared43Bytes_eq : shared43Bytes = encode Sign14PrefixCode.shared43 := by
  unfold shared43Bytes
  simp only [shared42Bytes_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared40Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared41Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared42Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared43Bytes_eq
