import DiophantineConsistency.Sign14PrefixDagDecode01

/-! SOURCE-ONLY: decode the composed short-fragment row. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagDecode
open Sign14Prefix Sign14PrefixReflection Sign14PrefixCode Sign14PrefixDag

theorem row02_depth : depth Sign14PrefixCode.row02 ≤ 24 := by decide

theorem row02_decode (p : Fin 4 → ℤ) :
    decode p 24 row02Bytes = some (SharingSeed14Degree124.row02 p, []) := by
  rw [row02Bytes_eq]
  have h := decode_encode p Sign14PrefixCode.row02 24 row02_depth []
  simpa only [List.append_nil, row02_interpret] using h
end DiophantineConsistency.Sign14PrefixDagDecode
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row02_depth
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row02_decode
