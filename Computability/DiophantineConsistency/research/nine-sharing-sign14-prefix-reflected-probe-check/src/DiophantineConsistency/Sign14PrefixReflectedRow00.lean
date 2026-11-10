import DiophantineConsistency.Sign14PrefixCodeRow00

/-! SOURCE-ONLY: proposed compositional prefix-byte binding. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection Sign14Prefix

theorem row00_bytes : (include_str "row00.prefix").toList = encode row00 := by
  rfl

theorem row00_depth : depth row00 ≤ 24 := by decide

theorem row00_decode_reflected (p : Fin 4 → ℤ) :
    decode p 24 (include_str "row00.prefix").toList =
      some (SharingSeed14Degree124.row00 p, []) := by
  rw [row00_bytes]
  have h := decode_encode p row00 24 row00_depth []
  simpa only [List.append_nil, row00_interpret] using h
end DiophantineConsistency.Sign14PrefixCode
#print axioms DiophantineConsistency.Sign14PrefixCode.row00_bytes
#print axioms DiophantineConsistency.Sign14PrefixCode.row00_depth
#print axioms DiophantineConsistency.Sign14PrefixCode.row00_decode_reflected
