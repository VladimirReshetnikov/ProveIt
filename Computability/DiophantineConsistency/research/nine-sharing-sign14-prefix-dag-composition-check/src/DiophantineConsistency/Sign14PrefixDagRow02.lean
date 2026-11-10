import DiophantineConsistency.Sign14PrefixDagRow01

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def row02Bytes : List Char := ('-' :: (('-' :: (fragment026 ++ fragment027)) ++ fragment025))
theorem row02Bytes_eq : row02Bytes = encode Sign14PrefixCode.row02 := by
  unfold row02Bytes
  simp only [fragment026_eq, fragment027_eq, fragment025_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.row02Bytes_eq
