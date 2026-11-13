import DiophantineConsistency.Sign20AxisCoeffLemmas

/-! SOURCE-ONLY: diagnose boolean equality in finite p-dependent row counts. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20CountDiagnostic
open Sign20LeadingRows

set_option maxHeartbeats 4000000 in
theorem n0_count (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.remainingResiduals p).count (n0 p) = 1 := by
  simp [List.count_cons, beq_iff_eq, SharingSeed20Degree20.remainingResiduals,
    n0, dc2, e, u, a, delta]

set_option maxHeartbeats 4000000 in
theorem dc2_count (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.remainingResiduals p).count (dc2 p) = 1 := by
  simp [List.count_cons, beq_iff_eq, SharingSeed20Degree20.remainingResiduals,
    n0, dc2, e, u, a, delta]
end DiophantineConsistency.Sign20CountDiagnostic
#print axioms DiophantineConsistency.Sign20CountDiagnostic.n0_count
#print axioms DiophantineConsistency.Sign20CountDiagnostic.dc2_count
