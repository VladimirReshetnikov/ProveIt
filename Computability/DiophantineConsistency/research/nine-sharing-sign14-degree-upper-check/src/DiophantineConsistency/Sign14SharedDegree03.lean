import DiophantineConsistency.Sign14SharedDegree02

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem shared15_degree (p : Fin 4 → ℤ) : degree (shared15 p) ≤ 4 := by
  have h03 := shared03_degree p
  have h12 := shared12_degree p
  unfold shared15
  change (degree (shared03 p) + degree (shared12 p)) ≤ 4
  omega

set_option maxHeartbeats 4000000 in
theorem shared16_degree (p : Fin 4 → ℤ) : degree (shared16 p) ≤ 5 := by
  have h13 := shared13_degree p
  unfold shared16
  change (max (max (1) (0)) (max (1) (0)) + degree (shared13 p)) ≤ 5
  omega

set_option maxHeartbeats 4000000 in
theorem shared17_degree (p : Fin 4 → ℤ) : degree (shared17 p) ≤ 5 := by
  have h16 := shared16_degree p
  unfold shared17
  change max (degree (shared16 p)) (max (1) (0)) ≤ 5
  omega

set_option maxHeartbeats 4000000 in
theorem shared18_degree (p : Fin 4 → ℤ) : degree (shared18 p) ≤ 6 := by
  have h05 := shared05_degree p
  have h13 := shared13_degree p
  unfold shared18
  change (degree (shared05 p) + degree (shared13 p)) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared19_degree (p : Fin 4 → ℤ) : degree (shared19 p) ≤ 6 := by
  have h17 := shared17_degree p
  unfold shared19
  change (degree (shared17 p) + max (1) (0)) ≤ 6
  omega

end DiophantineConsistency.Sign14SyntaxDegree
