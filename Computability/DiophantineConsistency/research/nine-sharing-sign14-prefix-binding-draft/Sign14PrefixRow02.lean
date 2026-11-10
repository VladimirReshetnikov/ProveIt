import DiophantineConsistency.Sign14PrefixParser

/-! SOURCE-ONLY: proposed byte-to-staged-row binding, not checked yet. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Prefix

theorem row02_decode (p : Fin 4 → ℤ) :
    decode p 24 (include_str "row02.prefix").toList =
      some (SharingSeed14Degree124.row02 p, []) := by
  rfl
end DiophantineConsistency.Sign14Prefix
#print axioms DiophantineConsistency.Sign14Prefix.row02_decode
