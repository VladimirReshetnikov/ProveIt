import DiophantineConsistency.Sign14PrefixDagDecode02

/-! SOURCE-ONLY: decode the composed short-fragment row. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagDecode
open Sign14Prefix Sign14PrefixReflection Sign14PrefixCode Sign14PrefixDag

theorem row03_depth : depth Sign14PrefixCode.row03 ≤ 24 := by decide

theorem row03_decode (p : Fin 4 → ℤ) :
    decode p 24 row03Bytes = some (SharingSeed14Degree124.row03 p, []) := by
  rw [row03Bytes_eq]
  have h := decode_encode p Sign14PrefixCode.row03 24 row03_depth []
  simpa only [List.append_nil, row03_interpret] using h
end DiophantineConsistency.Sign14PrefixDagDecode
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row03_depth
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row03_decode
