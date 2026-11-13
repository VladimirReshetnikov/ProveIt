import DiophantineConsistency.Sign17SyntaxDegree

/-! SOURCE-ONLY: test compositional degree bounds for the first shared nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] shared00 shared01 shared02 shared03 shared04
  shared05 shared06 shared07 shared08 shared09 shared10 shared11 shared12 shared13 shared14
  shared15 shared16 shared17 shared18 shared19 shared20 shared21 shared22 shared23 shared24
  shared25 shared26 shared27 shared28 shared29 shared30 shared31 shared32 shared33 shared34

set_option maxHeartbeats 4000000 in
theorem shared00_degree (p : Fin 4 → ℤ) : degree (shared00 p) ≤ 1 := by
  unfold shared00
  simp only [degree]
  omega

set_option maxHeartbeats 4000000 in
theorem shared01_degree (p : Fin 4 → ℤ) : degree (shared01 p) ≤ 2 := by
  unfold shared01
  simp only [degree]
  omega

set_option maxHeartbeats 4000000 in
theorem shared02_degree (p : Fin 4 → ℤ) : degree (shared02 p) ≤ 2 := by
  unfold shared02
  simp only [degree]
  omega

set_option maxHeartbeats 4000000 in
theorem shared03_degree (p : Fin 4 → ℤ) : degree (shared03 p) ≤ 1 := by
  unfold shared03
  simp only [degree]
  omega

set_option maxHeartbeats 4000000 in
theorem shared04_degree (p : Fin 4 → ℤ) : degree (shared04 p) ≤ 1 := by
  have h := shared00_degree p
  unfold shared04
  simp only [degree]
  omega
end DiophantineConsistency.Sign17SyntaxDegree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.shared00_degree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.shared04_degree
