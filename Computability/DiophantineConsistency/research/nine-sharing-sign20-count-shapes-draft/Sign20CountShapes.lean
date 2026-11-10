import DiophantineConsistency.Sign20AxisCoeffLemmas

/-! SOURCE-ONLY: distinguish finite p-dependent residual shapes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20CountShapes
open Sign20LeadingRows

def row (p : Fin 4 → ℤ) (i : Fin 10) : Expr (Fin 21) :=
  (SharingSeed20Degree20.remainingResiduals p).get i

set_option maxHeartbeats 4000000 in
theorem n0_ne_0 (p : Fin 4 → ℤ) : n0 p ≠ row p 0 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_1 (p : Fin 4 → ℤ) : n0 p ≠ row p 1 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_2 (p : Fin 4 → ℤ) : n0 p ≠ row p 2 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_4 (p : Fin 4 → ℤ) : n0 p ≠ row p 4 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_5 (p : Fin 4 → ℤ) : n0 p ≠ row p 5 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_6 (p : Fin 4 → ℤ) : n0 p ≠ row p 6 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_7 (p : Fin 4 → ℤ) : n0 p ≠ row p 7 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_8 (p : Fin 4 → ℤ) : n0 p ≠ row p 8 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem n0_ne_9 (p : Fin 4 → ℤ) : n0 p ≠ row p 9 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_0 (p : Fin 4 → ℤ) : dc2 p ≠ row p 0 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_2 (p : Fin 4 → ℤ) : dc2 p ≠ row p 2 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_3 (p : Fin 4 → ℤ) : dc2 p ≠ row p 3 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_4 (p : Fin 4 → ℤ) : dc2 p ≠ row p 4 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_5 (p : Fin 4 → ℤ) : dc2 p ≠ row p 5 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_6 (p : Fin 4 → ℤ) : dc2 p ≠ row p 6 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_7 (p : Fin 4 → ℤ) : dc2 p ≠ row p 7 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_8 (p : Fin 4 → ℤ) : dc2 p ≠ row p 8 := by
  intro h
  cases h

set_option maxHeartbeats 4000000 in
theorem dc2_ne_9 (p : Fin 4 → ℤ) : dc2 p ≠ row p 9 := by
  intro h
  cases h

end DiophantineConsistency.Sign20CountShapes
#print axioms DiophantineConsistency.Sign20CountShapes.n0_ne_0
#print axioms DiophantineConsistency.Sign20CountShapes.dc2_ne_9
