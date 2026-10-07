import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation

namespace OAI

section

namespace Erdos3

noncomputable def secondaryBoundaryMargin (boundary beta : ℝ) : ℝ := replacementAccuracy boundary beta

noncomputable def secondaryMeshDelta (boundary movement beta : ℝ) : ℝ :=
  replacementAccuracy movement (secondaryBoundaryMargin boundary beta)

theorem secondaryMeshAllocation_spec {boundary movement beta : ℝ}
    (hboundary : 0 ≤ boundary) (hmovement : 0 ≤ movement) (hbeta : 0 < beta) :
    0 < secondaryBoundaryMargin boundary beta ∧ secondaryBoundaryMargin boundary beta ≤ 1 ∧
      boundary * secondaryBoundaryMargin boundary beta ≤ beta ∧
      0 < secondaryMeshDelta boundary movement beta ∧ secondaryMeshDelta boundary movement beta ≤ 1 ∧
      secondaryMeshDelta boundary movement beta * movement ≤ secondaryBoundaryMargin boundary beta := by
  have hm := replacementAccuracy_spec hboundary hbeta
  have hd := replacementAccuracy_spec hmovement hm.1
  exact ⟨hm.1, hm.2.1, hm.2.2, hd.1, hd.2.1, (mul_comm _ _).trans_le hd.2.2⟩

theorem secondaryMeshAllocation_inverse_bounds {boundary movement beta P : ℝ}
    (hboundary : 0 ≤ boundary) (hmovement : 0 ≤ movement) (hbeta : 0 < beta) (hP : 0 ≤ P)
    (hboundaryP : boundary ≤ Real.exp P) (hmovementP : movement ≤ Real.exp P)
    (hbetaP : beta⁻¹ ≤ Real.exp P) :
    (secondaryBoundaryMargin boundary beta)⁻¹ ≤ Real.exp (2 * P + 2) ∧
      (secondaryMeshDelta boundary movement beta)⁻¹ ≤ Real.exp (4 * P + 6) := by
  have hm := replacementAccuracy_inverse_le_exp hboundary hbeta hP hboundaryP hbetaP
  refine ⟨hm, ?_⟩
  have hmargin := (replacementAccuracy_spec hboundary hbeta).1
  have hmovement' : movement ≤ Real.exp (2 * P + 2) :=
    hmovementP.trans (Real.exp_le_exp.mpr (by linarith))
  have hd := replacementAccuracy_inverse_le_exp hmovement hmargin (by linarith : 0 ≤ 2 * P + 2)
    hmovement' hm
  exact hd.trans_eq (by congr 1; ring)

theorem secondaryMeshAllocation_size_bounds {boundary movement beta P H scale : ℝ}
    (hboundary : 0 ≤ boundary) (hmovement : 0 ≤ movement) (hbeta : 0 < beta) (hP : 0 ≤ P)
    (hboundaryP : boundary ≤ Real.exp P) (hmovementP : movement ≤ Real.exp P)
    (hbetaP : beta⁻¹ ≤ Real.exp P) (hH : Real.exp (2 * P + 2) ≤ H)
    (hscale : 4 * Real.exp (4 * P + 6) ≤ scale) :
    1 ≤ secondaryBoundaryMargin boundary beta * H ∧
      4 ≤ secondaryMeshDelta boundary movement beta * scale := by
  have hs := secondaryMeshAllocation_spec hboundary hmovement hbeta
  have hi := secondaryMeshAllocation_inverse_bounds hboundary hmovement hbeta hP hboundaryP hmovementP hbetaP
  constructor
  · have h := mul_le_mul_of_nonneg_left (hi.1.trans hH) hs.1.le
    simpa only [mul_inv_cancel₀ hs.1.ne'] using h
  · have hdiv : 4 / secondaryMeshDelta boundary movement beta ≤ scale := by
      calc
        _ = 4 * (secondaryMeshDelta boundary movement beta)⁻¹ := div_eq_mul_inv _ _
        _ ≤ 4 * Real.exp (4 * P + 6) := mul_le_mul_of_nonneg_left hi.2 (by norm_num)
        _ ≤ scale := hscale
    simpa only [mul_comm] using (div_le_iff₀ hs.2.2.2.1).mp hdiv

end Erdos3

end

section

namespace Erdos3

noncomputable def secondaryMovementBudget (movement sourceRatio parameterRatio : ℝ) : ℝ :=
  movement + sourceRatio + parameterRatio

theorem secondaryMesh_geometry {boundary movement sourceRatio parameterRatio beta : ℝ}
    (hb : 0 ≤ boundary) (hm : 0 ≤ movement) (hs : 0 ≤ sourceRatio) (hp : 0 ≤ parameterRatio)
    (hbeta : 0 < beta) :
    let M := secondaryMovementBudget movement sourceRatio parameterRatio
    let margin := secondaryBoundaryMargin boundary beta
    let delta := secondaryMeshDelta boundary M beta
    0 < margin ∧ margin ≤ 1 ∧ boundary * margin ≤ beta ∧
      0 < delta ∧ delta ≤ 1 ∧ delta * movement ≤ margin ∧
      delta * sourceRatio ≤ 1 ∧ delta * parameterRatio ≤ 1 := by
  intro M margin delta
  have hM : 0 ≤ M := by dsimp only [M, secondaryMovementBudget]; positivity
  have h := secondaryMeshAllocation_spec hb hM hbeta
  change 0 < margin ∧ margin ≤ 1 ∧ boundary * margin ≤ beta ∧
    0 < delta ∧ delta ≤ 1 ∧ delta * M ≤ margin at h
  have hmM : movement ≤ M := by dsimp only [M, secondaryMovementBudget]; linarith
  have hsM : sourceRatio ≤ M := by dsimp only [M, secondaryMovementBudget]; linarith
  have hpM : parameterRatio ≤ M := by dsimp only [M, secondaryMovementBudget]; linarith
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    (mul_le_mul_of_nonneg_left hmM h.2.2.2.1.le).trans h.2.2.2.2.2,
    ((mul_le_mul_of_nonneg_left hsM h.2.2.2.1.le).trans h.2.2.2.2.2).trans h.2.1,
    ((mul_le_mul_of_nonneg_left hpM h.2.2.2.1.le).trans h.2.2.2.2.2).trans h.2.1⟩

theorem secondaryMovementBudget_le_exp {movement sourceRatio parameterRatio P : ℝ}
    (hm : movement ≤ Real.exp P) (hs : sourceRatio ≤ Real.exp P)
    (hp : parameterRatio ≤ Real.exp P) :
    secondaryMovementBudget movement sourceRatio parameterRatio ≤ Real.exp (P + 3) := by
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  rw [Real.exp_add]
  have h := mul_le_mul_of_nonneg_left hthree (Real.exp_nonneg P)
  unfold secondaryMovementBudget
  linarith

theorem normalizedMesh_upper_of_ratio {delta scale ratio : ℝ} (N : ℕ)
    (hdelta : 0 ≤ delta) (hbudget : delta * ratio ≤ 1)
    (hscale : scale ≤ ratio * (N : ℝ)) : delta * scale ≤ 2 * (N : ℝ) := by
  have h := mul_le_mul_of_nonneg_left hscale hdelta
  have h' := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N)
  nlinarith

end Erdos3

end

end OAI
