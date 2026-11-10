import DiophantineConsistency.Sign14PrefixDagShared08

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def row00Bytes : List Char := ('-' :: (shared41Bytes ++ ('*' :: (shared40Bytes ++ ('*' :: (shared17Bytes ++ shared17Bytes))))))
theorem row00Bytes_eq : row00Bytes = encode Sign14PrefixCode.row00 := by
  unfold row00Bytes
  simp only [shared41Bytes_eq, shared40Bytes_eq, shared17Bytes_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.row00Bytes_eq
