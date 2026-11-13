import DiophantineConsistency.Sign14PrefixCodeRow00

/-! SOURCE-ONLY: a separate short included file at a shared-node boundary. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixFragment00
open Sign14PrefixReflection Sign14PrefixCode

theorem shared07_bytes : encode shared07 = "+*j+*B+b11*B+b1".toList := by
  rfl

theorem fragment_bytes : (include_str "chunk00.prefix").toList =
    '-' :: '*' :: '+' :: '+' :: encode shared07 := by
  rw [shared07_bytes]
  rfl
end DiophantineConsistency.Sign14PrefixFragment00
#print axioms DiophantineConsistency.Sign14PrefixFragment00.shared07_bytes
#print axioms DiophantineConsistency.Sign14PrefixFragment00.fragment_bytes
