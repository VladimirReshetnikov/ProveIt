import OAI.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData

namespace OAI

section

namespace Erdos3

noncomputable def scalarMeshLog (gridLog inputLog accuracyLog : ℝ) : ℝ :=
  gridLog + 3 * inputLog + accuracyLog + 50

theorem scalarMeshLog_bounds {G P T : ℝ} (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T) :
    0 ≤ scalarMeshLog G P T ∧ P ≤ scalarMeshLog G P T ∧ T ≤ scalarMeshLog G P T ∧
      G + 3 * P + 40 ≤ scalarMeshLog G P T ∧ 2 * P + 3 ≤ scalarMeshLog G P T := by
  unfold scalarMeshLog
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

theorem scalarMesh_boundary_bound {n A rho c G P T : ℝ}
    (hn : 0 ≤ n) (hA : 0 ≤ A) (hrho : 0 < rho) (hc : 0 < c)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hnP : n ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrhoG : rho⁻¹ ≤ Real.exp G) (hcP : c⁻¹ ≤ Real.exp P) :
    40 * n * A / (rho * c) ≤ Real.exp (scalarMeshLog G P T) := by
  have h40 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have hproduct : 40 * n * A * rho⁻¹ * c⁻¹ ≤
      Real.exp 40 * Real.exp P * Real.exp P * Real.exp G * Real.exp P := by
    gcongr
  calc
    _ = 40 * n * A * rho⁻¹ * c⁻¹ := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := hproduct
    _ = Real.exp (G + 3 * P + 40) := by simp only [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (scalarMeshLog_bounds hG hP hT).2.2.2.1

theorem scalarMesh_movement_bound {d C B G P T : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hdP : d ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hBP : B ≤ Real.exp P) :
    1 + d * (C + B) ≤ Real.exp (scalarMeshLog G P T) := by
  have hmul : d * (C + B) ≤ Real.exp P * (Real.exp P + Real.exp P) := by gcongr
  have h1 : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have heq : Real.exp P * (Real.exp P + Real.exp P) = 2 * Real.exp (2 * P) := by
    rw [show 2 * P = P + P by ring, Real.exp_add]; ring
  rw [heq] at hmul
  calc
    _ ≤ 3 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 3 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = Real.exp (2 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (scalarMeshLog_bounds hG hP hT).2.2.2.2

end Erdos3

end

end OAI
