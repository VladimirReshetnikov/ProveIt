import DiophantineConsistency.Sign14PrefixDagRow04

/-! SOURCE-ONLY: decode the composed short-fragment row. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagDecode
open Sign14Prefix Sign14PrefixReflection Sign14PrefixCode Sign14PrefixDag

theorem row00_depth : depth Sign14PrefixCode.row00 ≤ 24 := by decide

theorem row00_decode (p : Fin 4 → ℤ) :
    decode p 24 row00Bytes = some (SharingSeed14Degree124.row00 p, []) := by
  rw [row00Bytes_eq]
  have h := decode_encode p Sign14PrefixCode.row00 24 row00_depth []
  simpa only [List.append_nil, row00_interpret] using h
end DiophantineConsistency.Sign14PrefixDagDecode
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row00_depth
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row00_decode
