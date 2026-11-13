import DiophantineConsistency.Sign17SharedDegree04

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem shared25_degree (p : Fin 4 → ℤ) : degree (shared25 p) ≤ 11 := by
  have h16 := shared16_degree p
  have h18 := shared18_degree p
  unfold shared25
  change (degree (shared18 p) + degree (shared16 p)) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared26_degree (p : Fin 4 → ℤ) : degree (shared26 p) ≤ 11 := by
  have h17 := shared17_degree p
  have h20 := shared20_degree p
  unfold shared26
  change (degree (shared20 p) + degree (shared17 p)) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared27_degree (p : Fin 4 → ℤ) : degree (shared27 p) ≤ 11 := by
  have h07 := shared07_degree p
  have h26 := shared26_degree p
  unfold shared27
  change max (degree (shared07 p)) (degree (shared26 p)) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared28_degree (p : Fin 4 → ℤ) : degree (shared28 p) ≤ 12 := by
  have h20 := shared20_degree p
  unfold shared28
  change (degree (shared20 p) + degree (shared20 p)) ≤ 12
  omega

set_option maxHeartbeats 4000000 in
theorem shared29_degree (p : Fin 4 → ℤ) : degree (shared29 p) ≤ 11 := by
  have h24 := shared24_degree p
  have h27 := shared27_degree p
  unfold shared29
  change max (degree (shared27 p)) (degree (shared24 p)) ≤ 11
  omega

end DiophantineConsistency.Sign17SyntaxDegree
