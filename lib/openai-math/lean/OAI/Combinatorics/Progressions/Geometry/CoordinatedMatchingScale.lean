import OAI.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget

namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

noncomputable def coordinatedMatchingScale (rank : ℕ) (M delta c : ℝ)
    (kappa : ℝ≥0) : ℝ≥0 :=
  min (kappa / 2) (min (controlledLocalMomentScale rank M delta)
    (localizedAverageScale rank (M ^ 2) (c / 32) / 2))

theorem coordinatedMatchingScale_spec (rank : ℕ) {M delta c : ℝ} {kappa : ℝ≥0}
    (hM : 0 ≤ M) (hdelta : 0 < delta) (hc : 0 < c) (hkappa : 0 < kappa) :
    0 < coordinatedMatchingScale rank M delta c kappa ∧
      coordinatedMatchingScale rank M delta c kappa ≤ kappa / 2 ∧
      coordinatedMatchingScale rank M delta c kappa ≤ controlledLocalMomentScale rank M delta ∧
      coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max rank 1 : ℕ) *
        ((coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa : ℝ≥0) : ℝ)) ≤
          c / 32 := by
  obtain ⟨hmoment, _, _⟩ := controlledLocalMomentScale_spec rank hM hdelta
  obtain ⟨hboundary, hsmall, herror⟩ := localizedAverageScale_spec rank (sq_nonneg M)
    (show 0 < c / 32 by positivity)
  have hleft : coordinatedMatchingScale rank M delta c kappa ≤ kappa / 2 := min_le_left _ _
  have hmomentBound : coordinatedMatchingScale rank M delta c kappa ≤
      controlledLocalMomentScale rank M delta := (min_le_right _ _).trans (min_le_left _ _)
  have hboundaryBound : coordinatedMatchingScale rank M delta c kappa ≤
      localizedAverageScale rank (M ^ 2) (c / 32) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsum : coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa ≤
      localizedAverageScale rank (M ^ 2) (c / 32) := by
    simpa only [add_halves] using add_le_add hboundaryBound hboundaryBound
  refine ⟨lt_min (div_pos hkappa (by norm_num)) (lt_min hmoment (div_pos hboundary (by norm_num))),
    hleft, hmomentBound, hsum.trans hsmall, ?_⟩
  have hsumR : ((coordinatedMatchingScale rank M delta c kappa + coordinatedMatchingScale rank M delta c kappa : ℝ≥0) : ℝ) ≤
      localizedAverageScale rank (M ^ 2) (c / 32) := by exact_mod_cast hsum
  apply le_trans _ herror
  gcongr

noncomputable def coordinatedMatchingScaleLoss (rank : ℕ) (P K delta c : ℝ) : ℝ :=
  K + rank + 2 * P + localMomentErrorBudget delta + unbalancedErrorBudget c + 1604

theorem coordinatedMatchingScale_exp_lower (rank : ℕ)
    {M P K delta c : ℝ} {kappa : ℝ≥0}
    (hM : 0 ≤ M) (hcap : M ≤ Real.exp P) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hdelta : 0 < delta) (hc : 0 < c) (hc1 : c ≤ 1)
    (hkappa : Real.exp (-K) ≤ (kappa : ℝ)) :
    Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      (coordinatedMatchingScale rank M delta c kappa : ℝ) := by
  have hEd := (localMomentErrorBudget_spec hdelta).1
  obtain ⟨hEc, hEceq⟩ := unbalancedErrorBudget_spec hc hc1
  have hmoment := controlledLocalMomentScale_exp_lower rank hM hcap hP hdelta
  have hMtwo : M ^ 2 ≤ Real.exp (2 * P) := by
    calc
      _ ≤ (Real.exp P) ^ 2 := pow_le_pow_left₀ hM hcap 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hboundary := localizedAverageScale_exp_lower_of_error rank (sq_nonneg M) hMtwo
    (show 0 ≤ 2 * P by positivity) hEc
    (show Real.exp (-unbalancedErrorBudget c) / 2 ≤ c / 32 by rw [hEceq]; linarith)
  have htwo : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    have h : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) h
  have hhalf {a : ℝ} {r : ℝ≥0} (ha : Real.exp (-a) ≤ (r : ℝ)) :
      Real.exp (-(a + 2)) ≤ ((r / 2 : ℝ≥0) : ℝ) := by
    calc
      _ = Real.exp (-a) * Real.exp (-2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (r : ℝ) * (1 / 2) := mul_le_mul ha htwo (Real.exp_nonneg _) r.coe_nonneg
      _ = _ := by change _ = (r : ℝ) / 2; ring
  have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
  have houter : Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      ((kappa / 2 : ℝ≥0) : ℝ) := by
    apply le_trans _ (hhalf hkappa)
    apply Real.exp_le_exp.mpr
    unfold coordinatedMatchingScaleLoss
    linarith
  have hmom : Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      (controlledLocalMomentScale rank M delta : ℝ) := by
    apply le_trans _ hmoment
    apply Real.exp_le_exp.mpr
    unfold coordinatedMatchingScaleLoss
    linarith
  have hbound : Real.exp (-coordinatedMatchingScaleLoss rank P K delta c) ≤
      ((localizedAverageScale rank (M ^ 2) (c / 32) / 2 : ℝ≥0) : ℝ) := by
    apply le_trans _ (hhalf hboundary)
    apply Real.exp_le_exp.mpr
    unfold coordinatedMatchingScaleLoss
    linarith
  change _ ≤ min ((kappa / 2 : ℝ≥0) : ℝ)
    (min (controlledLocalMomentScale rank M delta : ℝ)
      ((localizedAverageScale rank (M ^ 2) (c / 32) / 2 : ℝ≥0) : ℝ))
  exact le_min houter (le_min hmom hbound)

end Erdos3.CellRefinement

end

end OAI
