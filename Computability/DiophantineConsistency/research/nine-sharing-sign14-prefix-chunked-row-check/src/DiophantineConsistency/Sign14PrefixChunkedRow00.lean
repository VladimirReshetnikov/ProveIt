import DiophantineConsistency.Sign14PrefixCodeRow00

/-! SOURCE-ONLY: assemble separate short included chunks, not the original String. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixChunkedRow
open Sign14PrefixReflection Sign14Prefix Sign14PrefixCode

def chunked : List Char :=
    (include_str "chunk00.prefix").toList ++
    (include_str "chunk01.prefix").toList ++
    (include_str "chunk02.prefix").toList ++
    (include_str "chunk03.prefix").toList ++
    (include_str "chunk04.prefix").toList ++
    (include_str "chunk05.prefix").toList ++
    (include_str "chunk06.prefix").toList ++
    (include_str "chunk07.prefix").toList ++
    (include_str "chunk08.prefix").toList ++
    (include_str "chunk09.prefix").toList ++
    (include_str "chunk10.prefix").toList ++
    (include_str "chunk11.prefix").toList ++
    (include_str "chunk12.prefix").toList ++
    (include_str "chunk13.prefix").toList ++
    (include_str "chunk14.prefix").toList ++
    (include_str "chunk15.prefix").toList ++
    (include_str "chunk16.prefix").toList ++
    (include_str "chunk17.prefix").toList ++
    (include_str "chunk18.prefix").toList ++
    (include_str "chunk19.prefix").toList ++
    (include_str "chunk20.prefix").toList ++
    (include_str "chunk21.prefix").toList ++ []

theorem chunks_bytes : chunked = encode row00 := by
  rfl

theorem row_depth : depth row00 ≤ 24 := by decide

theorem decode_chunked (p : Fin 4 → ℤ) :
    decode p 24 chunked = some (SharingSeed14Degree124.row00 p, []) := by
  rw [chunks_bytes]
  have h := decode_encode p row00 24 row_depth []
  simpa only [List.append_nil, row00_interpret] using h
end DiophantineConsistency.Sign14PrefixChunkedRow
#print axioms DiophantineConsistency.Sign14PrefixChunkedRow.chunks_bytes
#print axioms DiophantineConsistency.Sign14PrefixChunkedRow.row_depth
#print axioms DiophantineConsistency.Sign14PrefixChunkedRow.decode_chunked
