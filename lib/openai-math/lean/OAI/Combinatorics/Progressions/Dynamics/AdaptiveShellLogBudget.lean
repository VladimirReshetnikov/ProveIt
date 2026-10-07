import OAI.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff

namespace OAI

section

namespace Erdos3

noncomputable def affineCountLogBudget (P : ℝ) : ℝ :=
  P * (affinePrimitiveLogBudget P + 2 * P ^ 2 + 1)

noncomputable def affineShellLogBudget (P : ℝ) : ℝ := P + affineCountLogBudget P

theorem affineShellLogBudget_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineCountLogBudget P ∧ 0 ≤ affineShellLogBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hc : 0 ≤ affineCountLogBudget P := by unfold affineCountLogBudget; positivity
  exact ⟨hc, add_nonneg hP hc⟩

theorem adaptiveAffineCountLog_le_budget (A sourceDim siteDim : ℕ)
    {epsilon L T C modLog P : ℝ} (hP : 0 ≤ P) (hmod0 : 0 ≤ modLog)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hscale0 : 0 ≤ affineComparisonScale epsilon L T C)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P) :
    adaptiveAffineCountLog A sourceDim siteDim epsilon L T C modLog ≤ affineCountLogBudget P := by
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hi : affineComparisonScale epsilon L T C + (sourceDim : ℝ) * modLog +
      (siteDim : ℝ) * modLog + 1 ≤ affinePrimitiveLogBudget P + 2 * P ^ 2 + 1 := by nlinarith
  unfold adaptiveAffineCountLog affineCountLogBudget
  exact mul_le_mul hA hi (by positivity) hP

theorem adaptiveAffineShell_inverse_le_budget (A sourceDim siteDim : ℕ)
    {epsilon L T C modLog totalShell P : ℝ}
    (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P)
    (hcount : adaptiveAffineCountLog A sourceDim siteDim epsilon L T C modLog ≤ affineCountLogBudget P) :
    (adaptiveAffineShell A sourceDim siteDim epsilon L T C totalShell modLog)⁻¹ ≤
      Real.exp (affineShellLogBudget P) := by
  simp only [adaptiveAffineShell, mul_inv_rev, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp (affineCountLogBudget P) * Real.exp P :=
      mul_le_mul (Real.exp_le_exp.mpr hcount) htotalInv (inv_nonneg.mpr htotal.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold affineShellLogBudget; ring

end Erdos3

end

end OAI
