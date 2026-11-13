import DiophantineConsistency.Sign14SharedDegree06

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem shared35_degree (p : Fin 4 → ℤ) : degree (shared35 p) ≤ 8 := by
  have h34 := shared34_degree p
  unfold shared35
  change ((max (1) (0) + max (1) (0)) + degree (shared34 p)) ≤ 8
  omega

set_option maxHeartbeats 4000000 in
theorem shared36_degree (p : Fin 4 → ℤ) : degree (shared36 p) ≤ 7 := by
  have h27 := shared27_degree p
  have h30 := shared30_degree p
  unfold shared36
  change max (degree (shared30 p)) (degree (shared27 p)) ≤ 7
  omega

set_option maxHeartbeats 4000000 in
theorem shared37_degree (p : Fin 4 → ℤ) : degree (shared37 p) ≤ 8 := by
  have h17 := shared17_degree p
  have h35 := shared35_degree p
  unfold shared37
  change max (degree (shared35 p)) (degree (shared17 p)) ≤ 8
  omega

set_option maxHeartbeats 4000000 in
theorem shared38_degree (p : Fin 4 → ℤ) : degree (shared38 p) ≤ 11 := by
  have h28 := shared28_degree p
  have h32 := shared32_degree p
  unfold shared38
  change max (degree (shared32 p)) (degree (shared28 p)) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared39_degree (p : Fin 4 → ℤ) : degree (shared39 p) ≤ 11 := by
  have h38 := shared38_degree p
  unfold shared39
  change max (degree (shared38 p)) (0) ≤ 11
  omega

end DiophantineConsistency.Sign14SyntaxDegree
