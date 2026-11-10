import DiophantineConsistency.Sign14SharedDegree03

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem shared20_degree (p : Fin 4 → ℤ) : degree (shared20 p) ≤ 7 := by
  have h18 := shared18_degree p
  unfold shared20
  change (degree (shared18 p) + max (1) (0)) ≤ 7
  omega

set_option maxHeartbeats 4000000 in
theorem shared21_degree (p : Fin 4 → ℤ) : degree (shared21 p) ≤ 7 := by
  have h20 := shared20_degree p
  unfold shared21
  change max (degree (shared20 p)) (max (max (1) (0)) (max (1) (0))) ≤ 7
  omega

set_option maxHeartbeats 4000000 in
theorem shared22_degree (p : Fin 4 → ℤ) : degree (shared22 p) ≤ 4 := by
  have h11 := shared11_degree p
  have h15 := shared15_degree p
  unfold shared22
  change max (degree (shared15 p)) (degree (shared11 p)) ≤ 4
  omega

set_option maxHeartbeats 4000000 in
theorem shared23_degree (p : Fin 4 → ℤ) : degree (shared23 p) ≤ 6 := by
  have h13 := shared13_degree p
  have h18 := shared18_degree p
  unfold shared23
  change max (degree (shared18 p)) (degree (shared13 p)) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared24_degree (p : Fin 4 → ℤ) : degree (shared24 p) ≤ 6 := by
  have h23 := shared23_degree p
  unfold shared24
  change (0 + degree (shared23 p)) ≤ 6
  omega

end DiophantineConsistency.Sign14SyntaxDegree
