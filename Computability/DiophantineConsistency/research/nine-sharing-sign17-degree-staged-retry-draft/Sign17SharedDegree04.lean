import DiophantineConsistency.Sign17SharedDegree03

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem shared20_degree (p : Fin 4 → ℤ) : degree (shared20 p) ≤ 6 := by
  have h13 := shared13_degree p
  have h18 := shared18_degree p
  unfold shared20
  change max (degree (shared18 p)) (degree (shared13 p)) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared21_degree (p : Fin 4 → ℤ) : degree (shared21 p) ≤ 6 := by
  have h20 := shared20_degree p
  unfold shared21
  change (0 + degree (shared20 p)) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared22_degree (p : Fin 4 → ℤ) : degree (shared22 p) ≤ 6 := by
  have h21 := shared21_degree p
  unfold shared22
  change max (degree (shared21 p)) (0) ≤ 6
  omega

set_option maxHeartbeats 4000000 in
theorem shared23_degree (p : Fin 4 → ℤ) : degree (shared23 p) ≤ 4 := by
  have h09 := shared09_degree p
  have h19 := shared19_degree p
  unfold shared23
  change max (degree (shared19 p)) (degree (shared09 p)) ≤ 4
  omega

set_option maxHeartbeats 4000000 in
theorem shared24_degree (p : Fin 4 → ℤ) : degree (shared24 p) ≤ 7 := by
  have h22 := shared22_degree p
  unfold shared24
  change (max (1) (0) + degree (shared22 p)) ≤ 7
  omega

end DiophantineConsistency.Sign17SyntaxDegree
