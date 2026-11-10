import DiophantineConsistency.Compact44.ArithmeticConstructionUnitCompact44
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSGammaOrder
open DiophantineConsistency.ArithmeticConstructionUnitCompact44

theorem gamma_order : 299052170727 ^ 581196 % 342946332593 = 1 := by
  apply nat_mod_of_zmod _ _ _ (by norm_num)
  rw [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char
#print axioms DirectBFSGammaOrder.gamma_order
end DirectBFSGammaOrder
