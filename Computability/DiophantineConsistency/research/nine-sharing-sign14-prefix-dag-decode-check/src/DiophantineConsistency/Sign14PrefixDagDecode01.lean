import DiophantineConsistency.Sign14PrefixDagDecode00

/-! SOURCE-ONLY: decode the composed short-fragment row. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagDecode
open Sign14Prefix Sign14PrefixReflection Sign14PrefixCode Sign14PrefixDag

theorem row01_depth : depth Sign14PrefixCode.row01 ≤ 24 := by decide

theorem row01_decode (p : Fin 4 → ℤ) :
    decode p 24 row01Bytes = some (SharingSeed14Degree124.row01 p, []) := by
  rw [row01Bytes_eq]
  have h := decode_encode p Sign14PrefixCode.row01 24 row01_depth []
  simpa only [List.append_nil, row01_interpret] using h
end DiophantineConsistency.Sign14PrefixDagDecode
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row01_depth
#print axioms DiophantineConsistency.Sign14PrefixDagDecode.row01_decode
