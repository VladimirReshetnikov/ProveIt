import DiophantineConsistency.Sign14PrefixDagDecode03

/-! SOURCE-ONLY: decode the composed short-fragment row. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagDecode
open Sign14Prefix Sign14PrefixReflection Sign14PrefixCode Sign14PrefixDag

theorem row04_depth : depth Sign14PrefixCode.row04 ≤ 24 := by decide

theorem row04_decode (p : Fin 4 → ℤ) :
    decode p 24 row04Bytes = some (SharingSeed14Degree124.row04 p, []) := by
  rw [row04Bytes_eq]
  have h := decode_encode p Sign14PrefixCode.row04 24 row04_depth []
  simpa only [List.append_nil, row04_interpret] using h
end DiophantineConsistency.Sign14PrefixDagDecode
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row04_depth
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row04_decode
