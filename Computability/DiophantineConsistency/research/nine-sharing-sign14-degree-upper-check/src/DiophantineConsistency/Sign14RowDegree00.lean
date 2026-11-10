import DiophantineConsistency.Sign14SharedDegree08

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem row00_degree (p : Fin 4 → ℤ) : degree (row00 p) ≤ 22 := by
  have h17 := shared17_degree p
  have h40 := shared40_degree p
  have h41 := shared41_degree p
  unfold row00
  change max (degree (shared41 p)) ((degree (shared40 p) + (degree (shared17 p) + degree (shared17 p)))) ≤ 22
  omega

end DiophantineConsistency.Sign14SyntaxDegree
