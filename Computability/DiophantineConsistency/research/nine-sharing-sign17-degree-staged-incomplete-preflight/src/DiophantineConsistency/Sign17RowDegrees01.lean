import DiophantineConsistency.Sign17RowDegrees00

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem row04_degree (p : Fin 4 → ℤ) : degree (row04 p) ≤ 6 := by
  have h14 := shared14_degree p
  have h17 := shared17_degree p
  have h23 := shared23_degree p
  unfold row04
  first
  | change 6 ≤ 6; decide
  | simp only [degree]; omega

set_option maxHeartbeats 4000000 in
theorem row05_degree (p : Fin 4 → ℤ) : degree (row05 p) ≤ 5 := by
  have h17 := shared17_degree p
  unfold row05
  first
  | change 5 ≤ 5; decide
  | simp only [degree]; omega

set_option maxHeartbeats 4000000 in
theorem row06_degree (p : Fin 4 → ℤ) : degree (row06 p) ≤ 48 := by
  have h34 := shared34_degree p
  unfold row06
  first
  | change 48 ≤ 48; decide
  | simp only [degree]; omega

set_option maxHeartbeats 4000000 in
theorem row07_degree (p : Fin 4 → ℤ) : degree (row07 p) ≤ 46 := by
  have h31 := shared31_degree p
  have h34 := shared34_degree p
  unfold row07
  first
  | change 46 ≤ 46; decide
  | simp only [degree]; omega

end DiophantineConsistency.Sign17SyntaxDegree
