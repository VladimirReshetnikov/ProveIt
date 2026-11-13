import DiophantineConsistency.Sign14RowDegree00

/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04 shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14 shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24 shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34 shared35 shared36 shared37 shared38 shared39 shared40 shared41 shared42 shared43 row00 row01 row02 row03 row04

set_option maxHeartbeats 4000000 in
theorem row01_degree (p : Fin 4 → ℤ) : degree (row01 p) ≤ 22 := by
  have h29 := shared29_degree p
  have h36 := shared36_degree p
  unfold row01
  change max (max ((degree (shared36 p) + degree (shared36 p))) ((degree (shared29 p) + max (degree (shared29 p)) (max (max (1) (0)) (max (1) (0)))))) (0) ≤ 22
  omega

end DiophantineConsistency.Sign14SyntaxDegree
