import DiophantineConsistency.Sign14PrefixDagRow03

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def row04Bytes : List Char := ('-' :: (('-' :: (('*' :: (shared40Bytes ++ fragment022)) ++ shared43Bytes)) ++ shared40Bytes))
theorem row04Bytes_eq : row04Bytes = encode Sign14PrefixCode.row04 := by
  unfold row04Bytes
  simp only [shared40Bytes_eq, fragment022_eq, shared43Bytes_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.row04Bytes_eq
