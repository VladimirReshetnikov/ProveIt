import DiophantineConsistency.Sign17SharedDegree05

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem shared30_degree (p : Fin 4 → ℤ) : degree (shared30 p) ≤ 11 := by
  have h29 := shared29_degree p
  unfold shared30
  change max (degree (shared29 p)) (0) ≤ 11
  omega

set_option maxHeartbeats 4000000 in
theorem shared31_degree (p : Fin 4 → ℤ) : degree (shared31 p) ≤ 12 := by
  have h22 := shared22_degree p
  have h28 := shared28_degree p
  unfold shared31
  change max (degree (shared28 p)) (degree (shared22 p)) ≤ 12
  omega

set_option maxHeartbeats 4000000 in
theorem shared32_degree (p : Fin 4 → ℤ) : degree (shared32 p) ≤ 22 := by
  have h29 := shared29_degree p
  have h30 := shared30_degree p
  unfold shared32
  change (degree (shared29 p) + degree (shared30 p)) ≤ 22
  omega

set_option maxHeartbeats 4000000 in
theorem shared33_degree (p : Fin 4 → ℤ) : degree (shared33 p) ≤ 23 := by
  have h32 := shared32_degree p
  unfold shared33
  change (max (1) (0) + degree (shared32 p)) ≤ 23
  omega

set_option maxHeartbeats 4000000 in
theorem shared34_degree (p : Fin 4 → ℤ) : degree (shared34 p) ≤ 46 := by
  have h33 := shared33_degree p
  unfold shared34
  change (degree (shared33 p) + degree (shared33 p)) ≤ 46
  omega

end DiophantineConsistency.Sign17SyntaxDegree
