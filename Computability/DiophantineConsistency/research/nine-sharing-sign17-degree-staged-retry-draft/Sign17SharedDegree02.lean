import DiophantineConsistency.Sign17SharedDegree01

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem shared10_degree (p : Fin 4 → ℤ) : degree (shared10 p) ≤ 2 := by
  have h06 := shared06_degree p
  unfold shared10
  change max (degree (shared06 p)) (max (1) (0)) ≤ 2
  omega

set_option maxHeartbeats 4000000 in
theorem shared11_degree (p : Fin 4 → ℤ) : degree (shared11 p) ≤ 3 := by
  have h08 := shared08_degree p
  unfold shared11
  change (max (max (1) (0)) (max (1) (0)) + degree (shared08 p)) ≤ 3
  omega

set_option maxHeartbeats 4000000 in
theorem shared12_degree (p : Fin 4 → ℤ) : degree (shared12 p) ≤ 3 := by
  have h08 := shared08_degree p
  unfold shared12
  change (degree (shared08 p) + max ((0 + max (1) (0))) (0)) ≤ 3
  omega

set_option maxHeartbeats 4000000 in
theorem shared13_degree (p : Fin 4 → ℤ) : degree (shared13 p) ≤ 4 := by
  have h12 := shared12_degree p
  unfold shared13
  change (max (1) (0) + degree (shared12 p)) ≤ 4
  omega

set_option maxHeartbeats 4000000 in
theorem shared14_degree (p : Fin 4 → ℤ) : degree (shared14 p) ≤ 2 := by
  have h01 := shared01_degree p
  have h10 := shared10_degree p
  unfold shared14
  change max (degree (shared10 p)) (degree (shared01 p)) ≤ 2
  omega

end DiophantineConsistency.Sign17SyntaxDegree
