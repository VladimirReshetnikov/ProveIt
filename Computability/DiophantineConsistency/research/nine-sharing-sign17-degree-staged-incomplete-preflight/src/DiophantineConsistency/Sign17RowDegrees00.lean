import DiophantineConsistency.Sign17SharedDegree06

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 row00 row01 row02 row03 row04 row05 row06 row07

set_option maxHeartbeats 4000000 in
theorem row00_degree (p : Fin 4 → ℤ) : degree (row00 p) ≤ 22 := by
  have h17 := shared17_degree p
  have h31 := shared31_degree p
  have h32 := shared32_degree p
  unfold row00
  first
  | change 22 ≤ 22; decide
  | simp only [degree]; omega

set_option maxHeartbeats 4000000 in
theorem row01_degree (p : Fin 4 → ℤ) : degree (row01 p) ≤ 7 := by
  have h14 := shared14_degree p
  have h18 := shared18_degree p
  have h23 := shared23_degree p
  unfold row01
  first
  | change 7 ≤ 7; decide
  | simp only [degree]; omega

set_option maxHeartbeats 4000000 in
theorem row02_degree (p : Fin 4 → ℤ) : degree (row02 p) ≤ 22 := by
  have h25 := shared25_degree p
  unfold row02
  first
  | change 22 ≤ 22; decide
  | simp only [degree]; omega

set_option maxHeartbeats 4000000 in
theorem row03_degree (p : Fin 4 → ℤ) : degree (row03 p) ≤ 2 := by
  unfold row03
  first
  | change 2 ≤ 2; decide
  | simp only [degree]; omega

end DiophantineConsistency.Sign17SyntaxDegree
