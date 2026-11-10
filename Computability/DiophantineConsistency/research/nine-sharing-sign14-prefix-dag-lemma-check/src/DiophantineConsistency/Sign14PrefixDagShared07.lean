import DiophantineConsistency.Sign14PrefixCodeRow00

/-! SOURCE-ONLY: first subtree-aligned included-file encoding lemma. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagShared07
open Sign14PrefixReflection Sign14PrefixCode

theorem shared07_fragment : (include_str "fragment007.prefix").toList = encode shared07 := by
  rfl
end DiophantineConsistency.Sign14PrefixDagShared07
#print axioms DiophantineConsistency.Sign14PrefixDagShared07.shared07_fragment
