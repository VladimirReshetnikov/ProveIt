import DiophantineConsistency.Sign14PrefixDagRow00

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def row01Bytes : List Char := ('-' :: (('-' :: (('*' :: (shared36Bytes ++ shared36Bytes)) ++ ('*' :: (shared29Bytes ++ ('+' :: (shared29Bytes ++ fragment015)))))) ++ fragment025))
theorem row01Bytes_eq : row01Bytes = encode Sign14PrefixCode.row01 := by
  unfold row01Bytes
  simp only [shared36Bytes_eq, shared29Bytes_eq, fragment015_eq, fragment025_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.row01Bytes_eq
