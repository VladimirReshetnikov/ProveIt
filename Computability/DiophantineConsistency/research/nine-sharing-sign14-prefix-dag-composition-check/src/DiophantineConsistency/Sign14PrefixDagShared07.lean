import DiophantineConsistency.Sign14PrefixDagShared06

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared35Bytes : List Char := ('*' :: (fragment022 ++ shared34Bytes))
theorem shared35Bytes_eq : shared35Bytes = encode Sign14PrefixCode.shared35 := by
  unfold shared35Bytes
  simp only [fragment022_eq, shared34Bytes_eq] <;> rfl

def shared36Bytes : List Char := ('-' :: (shared30Bytes ++ shared27Bytes))
theorem shared36Bytes_eq : shared36Bytes = encode Sign14PrefixCode.shared36 := by
  unfold shared36Bytes
  simp only [shared30Bytes_eq, shared27Bytes_eq] <;> rfl

def shared37Bytes : List Char := ('-' :: (shared35Bytes ++ shared17Bytes))
theorem shared37Bytes_eq : shared37Bytes = encode Sign14PrefixCode.shared37 := by
  unfold shared37Bytes
  simp only [shared35Bytes_eq, shared17Bytes_eq] <;> rfl

def shared38Bytes : List Char := ('+' :: (shared32Bytes ++ shared28Bytes))
theorem shared38Bytes_eq : shared38Bytes = encode Sign14PrefixCode.shared38 := by
  unfold shared38Bytes
  simp only [shared32Bytes_eq, shared28Bytes_eq] <;> rfl

def shared39Bytes : List Char := ('+' :: (shared38Bytes ++ fragment023))
theorem shared39Bytes_eq : shared39Bytes = encode Sign14PrefixCode.shared39 := by
  unfold shared39Bytes
  simp only [shared38Bytes_eq, fragment023_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared35Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared36Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared37Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared38Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared39Bytes_eq
