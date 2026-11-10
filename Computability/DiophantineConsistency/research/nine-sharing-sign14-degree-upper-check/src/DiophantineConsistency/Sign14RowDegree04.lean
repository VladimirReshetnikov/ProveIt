import DiophantineConsistency.Sign14RowDegree03

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem row04_degree (p : Fin 4 → ℤ) : degree (row04 p) ≤ 46 := by
  have h40 := shared40_degree p
  have h43 := shared43_degree p
  unfold row04
  change max (max ((degree (shared40 p) + (max (1) (0) + max (1) (0)))) (degree (shared43 p))) (degree (shared40 p)) ≤ 46
  omega

end DiophantineConsistency.Sign14SyntaxDegree
