import DiophantineConsistency.Sign20CountShapes

/-! SOURCE-ONLY: finite p-dependent counts from row-shape inequalities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20CountProof
open Sign20LeadingRows Sign20CountShapes

set_option maxHeartbeats 4000000 in
theorem n0_count (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.remainingResiduals p).count (n0 p) = 1 := by
  have hself : row p 3 = n0 p := by rfl
  have h0 : row p 0 ≠ n0 p := (n0_ne_0 p).symm
  have h1 : row p 1 ≠ n0 p := (n0_ne_1 p).symm
  have h2 : row p 2 ≠ n0 p := (n0_ne_2 p).symm
  have h4 : row p 4 ≠ n0 p := (n0_ne_4 p).symm
  have h5 : row p 5 ≠ n0 p := (n0_ne_5 p).symm
  have h6 : row p 6 ≠ n0 p := (n0_ne_6 p).symm
  have h7 : row p 7 ≠ n0 p := (n0_ne_7 p).symm
  have h8 : row p 8 ≠ n0 p := (n0_ne_8 p).symm
  have h9 : row p 9 ≠ n0 p := (n0_ne_9 p).symm
  change [row p 0, row p 1, row p 2, row p 3, row p 4, row p 5, row p 6, row p 7, row p 8, row p 9].count (n0 p) = 1
  simp [List.count_cons, beq_iff_eq, hself, h0, h1, h2, h4, h5, h6, h7, h8, h9]

set_option maxHeartbeats 4000000 in
theorem dc2_count (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.remainingResiduals p).count (dc2 p) = 1 := by
  have hself : row p 1 = dc2 p := by rfl
  have h0 : row p 0 ≠ dc2 p := (dc2_ne_0 p).symm
  have h2 : row p 2 ≠ dc2 p := (dc2_ne_2 p).symm
  have h3 : row p 3 ≠ dc2 p := (dc2_ne_3 p).symm
  have h4 : row p 4 ≠ dc2 p := (dc2_ne_4 p).symm
  have h5 : row p 5 ≠ dc2 p := (dc2_ne_5 p).symm
  have h6 : row p 6 ≠ dc2 p := (dc2_ne_6 p).symm
  have h7 : row p 7 ≠ dc2 p := (dc2_ne_7 p).symm
  have h8 : row p 8 ≠ dc2 p := (dc2_ne_8 p).symm
  have h9 : row p 9 ≠ dc2 p := (dc2_ne_9 p).symm
  change [row p 0, row p 1, row p 2, row p 3, row p 4, row p 5, row p 6, row p 7, row p 8, row p 9].count (dc2 p) = 1
  simp [List.count_cons, beq_iff_eq, hself, h0, h2, h3, h4, h5, h6, h7, h8, h9]

end DiophantineConsistency.Sign20CountProof
#print axioms DiophantineConsistency.Sign20CountProof.n0_count
#print axioms DiophantineConsistency.Sign20CountProof.dc2_count
