import DiophantineConsistency.Sign14PrefixCodeRow00

/-! SOURCE-ONLY: a first actual-file prefix at a shared-node boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixChunk00
open Sign14PrefixReflection Sign14PrefixCode

theorem shared07_bytes : encode shared07 = "+*j+*B+b11*B+b1".toList := by
  rfl

theorem file_head : ((include_str "row00.prefix").toList.take 19) =
    '-' :: '*' :: '+' :: '+' :: encode shared07 := by
  rw [shared07_bytes]
  rfl
end DiophantineConsistency.Sign14PrefixChunk00
#print axioms DiophantineConsistency.Sign14PrefixChunk00.shared07_bytes
#print axioms DiophantineConsistency.Sign14PrefixChunk00.file_head
