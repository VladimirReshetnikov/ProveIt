import DiophantineConsistency.Sign14PrefixDagRow02

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def row03Bytes : List Char := ('-' :: (('-' :: (fragment028 ++ ('*' :: (shared43Bytes ++ ('-' :: (fragment028 ++ ('*' :: (shared37Bytes ++ shared37Bytes)))))))) ++ fragment025))
theorem row03Bytes_eq : row03Bytes = encode Sign14PrefixCode.row03 := by
  unfold row03Bytes
  simp only [fragment028_eq, shared43Bytes_eq, shared37Bytes_eq, fragment025_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.row03Bytes_eq
