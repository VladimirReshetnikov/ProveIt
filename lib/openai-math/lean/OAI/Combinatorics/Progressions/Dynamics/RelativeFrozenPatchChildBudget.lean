import OAI.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent

namespace OAI

section

namespace Erdos3

theorem relativePatchComplexity_tail_le {X Y : Type*} {s D E : ℕ}
    (A : PolynomialPatch X s (D+E)) (B : PolynomialPatch Y s E)
    (hLip : B.kernel.lip = A.kernel.lip) :
    relativePatchComplexity B ≤ relativePatchComplexity A := by
  simp only [relativePatchComplexity, hLip, Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) D]

theorem relativeFrozenPatch_child_score_budget {p pchild gain : ℝ}
    (hgain : Real.exp (-p) ≤ gain) (hchild : p+2 ≤ pchild) :
    Real.exp (-pchild) ≤ 7*gain/16 := by
  have hg : 0 < gain := (Real.exp_pos _).trans_le hgain
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hprod : Real.exp (-(p+2)) * Real.exp 2 = Real.exp (-p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(p+2))).le
  apply (Real.exp_le_exp.mpr (neg_le_neg hchild)).trans
  nlinarith

end Erdos3

end

end OAI
