import DiophantineConsistency.Sign14SharedDegree05

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem shared30_degree (p : Fin 4 → ℤ) : degree (shared30 p) ≤ 7 := by
  have h14 := shared14_degree p
  have h21 := shared21_degree p
  unfold shared30
  change max (degree (shared21 p)) (degree (shared14 p)) ≤ 7
  omega

set_option maxHeartbeats 4000000 in
theorem shared31_degree (p : Fin 4 → ℤ) : degree (shared31 p) ≤ 11 := by
  have h17 := shared17_degree p
  have h23 := shared23_degree p
  unfold shared31
  change (degree (shared23 p) + degree (shared17 p)) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared32_degree (p : Fin 4 → ℤ) : degree (shared32 p) ≤ 11 := by
  have h07 := shared07_degree p
  have h31 := shared31_degree p
  unfold shared32
  change max (degree (shared07 p)) (degree (shared31 p)) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared33_degree (p : Fin 4 → ℤ) : degree (shared33 p) ≤ 12 := by
  have h23 := shared23_degree p
  unfold shared33
  change (degree (shared23 p) + degree (shared23 p)) ≤ 12
  omega

set_option maxHeartbeats 4000000 in
theorem shared34_degree (p : Fin 4 → ℤ) : degree (shared34 p) ≤ 6 := by
  have h25 := shared25_degree p
  have h27 := shared27_degree p
  unfold shared34
  change max (degree (shared25 p)) (degree (shared27 p)) ≤ 6
  omega

end DiophantineConsistency.Sign14SyntaxDegree
