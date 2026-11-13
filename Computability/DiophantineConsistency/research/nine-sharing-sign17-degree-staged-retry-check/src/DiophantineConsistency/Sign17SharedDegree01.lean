import DiophantineConsistency.Sign17SharedDegree00

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem shared05_degree (p : Fin 4 → ℤ) : degree (shared05 p) ≤ 2 := by
  unfold shared05
  change (max (1) (0) + max ((0 + max (1) (0))) (0)) ≤ 2
  omega

set_option maxHeartbeats 4000000 in
theorem shared06_degree (p : Fin 4 → ℤ) : degree (shared06 p) ≤ 2 := by
  unfold shared06
  change ((0 + max (1) (0)) + max ((0 + max (1) (0))) (0)) ≤ 2
  omega

set_option maxHeartbeats 4000000 in
theorem shared07_degree (p : Fin 4 → ℤ) : degree (shared07 p) ≤ 2 := by
  have h02 := shared02_degree p
  unfold shared07
  change max (degree (shared02 p)) ((0 + max (1) (0))) ≤ 2
  omega

set_option maxHeartbeats 4000000 in
theorem shared08_degree (p : Fin 4 → ℤ) : degree (shared08 p) ≤ 2 := by
  unfold shared08
  change (max ((0 + max (1) (0))) (0) + max ((0 + max (1) (0))) (0)) ≤ 2
  omega

set_option maxHeartbeats 4000000 in
theorem shared09_degree (p : Fin 4 → ℤ) : degree (shared09 p) ≤ 2 := by
  have h04 := shared04_degree p
  unfold shared09
  change (degree (shared04 p) + max (1) (0)) ≤ 2
  omega

end DiophantineConsistency.Sign17SyntaxDegree
