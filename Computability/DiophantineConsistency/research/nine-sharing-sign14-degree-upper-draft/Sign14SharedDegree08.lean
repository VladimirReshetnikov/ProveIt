import DiophantineConsistency.Sign14SharedDegree07

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem shared40_degree (p : Fin 4 → ℤ) : degree (shared40 p) ≤ 12 := by
  have h26 := shared26_degree p
  have h33 := shared33_degree p
  unfold shared40
  change max (degree (shared33 p)) (degree (shared26 p)) ≤ 12
  omega

set_option maxHeartbeats 4000000 in
theorem shared41_degree (p : Fin 4 → ℤ) : degree (shared41 p) ≤ 22 := by
  have h38 := shared38_degree p
  have h39 := shared39_degree p
  unfold shared41
  change (degree (shared38 p) + degree (shared39 p)) ≤ 22
  omega

set_option maxHeartbeats 4000000 in
theorem shared42_degree (p : Fin 4 → ℤ) : degree (shared42 p) ≤ 23 := by
  have h41 := shared41_degree p
  unfold shared42
  change (max (1) (0) + degree (shared41 p)) ≤ 23
  omega

set_option maxHeartbeats 4000000 in
theorem shared43_degree (p : Fin 4 → ℤ) : degree (shared43 p) ≤ 46 := by
  have h42 := shared42_degree p
  unfold shared43
  change (degree (shared42 p) + degree (shared42 p)) ≤ 46
  omega

end DiophantineConsistency.Sign14SyntaxDegree
