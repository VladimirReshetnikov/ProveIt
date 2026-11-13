import DiophantineConsistency.Sign14SharedDegree04

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem shared25_degree (p : Fin 4 → ℤ) : degree (shared25 p) ≤ 6 := by
  have h14 := shared14_degree p
  have h19 := shared19_degree p
  unfold shared25
  change max (degree (shared19 p)) (degree (shared14 p)) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared26_degree (p : Fin 4 → ℤ) : degree (shared26 p) ≤ 6 := by
  have h24 := shared24_degree p
  unfold shared26
  change max (degree (shared24 p)) (0) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared27_degree (p : Fin 4 → ℤ) : degree (shared27 p) ≤ 4 := by
  have h09 := shared09_degree p
  have h22 := shared22_degree p
  unfold shared27
  change max (degree (shared22 p)) (degree (shared09 p)) ≤ 4
  omega

set_option maxHeartbeats 4000000 in
theorem shared28_degree (p : Fin 4 → ℤ) : degree (shared28 p) ≤ 7 := by
  have h26 := shared26_degree p
  unfold shared28
  change (max (1) (0) + degree (shared26 p)) ≤ 7
  omega

set_option maxHeartbeats 4000000 in
theorem shared29_degree (p : Fin 4 → ℤ) : degree (shared29 p) ≤ 11 := by
  have h16 := shared16_degree p
  have h18 := shared18_degree p
  unfold shared29
  change (degree (shared18 p) + degree (shared16 p)) ≤ 11
  omega

end DiophantineConsistency.Sign14SyntaxDegree
