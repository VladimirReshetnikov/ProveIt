import OAI.Combinatorics.Progressions.Lattices.CRTWindowScore
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_representativeWindow_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p M sigma : ℝ, 0 ≤ p → 0 < M → M ≤ Real.exp p →
      Real.exp (-p) ≤ sigma →
      Real.log (2 + 100 * M / sigma + representativeWindowPartitionLip) ≤ (p + 2) ^ C ∧
      Real.exp (-((p + 2) ^ C)) ≤ 3 * sigma / (4 * representativeWindowCount) := by
  obtain ⟨a, ha⟩ := exists_nat_ge
    (Real.log (102 + (representativeWindowPartitionLip : ℝ)))
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.log (4 * (representativeWindowCount : ℝ)))
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (2 * Polynomial.X + Polynomial.C (a + b))
  refine ⟨C, hC, ?_⟩
  intro p M sigma hp hM hMexp hsigma
  have hspos : 0 < sigma := lt_of_lt_of_le (Real.exp_pos _) hsigma
  have hbudget : 2 * p + a + b ≤ (p + 2) ^ C := by
    simpa [Nat.cast_add, add_assoc] using hbound p hp
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hK : 0 ≤ (representativeWindowPartitionLip : ℝ) := NNReal.coe_nonneg _
  have hdiv : M / sigma ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p / Real.exp (-p) :=
        div_le_div₀ (Real.exp_pos _).le hMexp (Real.exp_pos _) hsigma
      _ = Real.exp (2 * p) := by rw [← Real.exp_sub]; congr 1; ring
  have he : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
  have hlip : 2 + 100 * M / sigma + representativeWindowPartitionLip ≤
      (102 + (representativeWindowPartitionLip : ℝ)) * Real.exp (2 * p) := by
    have hscaled := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 100)
    have hrest := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 +
      (representativeWindowPartitionLip : ℝ) by positivity)
    rw [mul_div_assoc]
    nlinarith
  have hcount : 0 < (4 * (representativeWindowCount : ℝ)) := by
    have : (0 : ℝ) < representativeWindowCount := by exact_mod_cast representativeWindowCount_pos
    positivity
  constructor
  · apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ (102 + (representativeWindowPartitionLip : ℝ)) * Real.exp (2 * p) := hlip
      _ = Real.exp (Real.log (102 + (representativeWindowPartitionLip : ℝ)) + 2 * p) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ Real.exp (-p - Real.log (4 * (representativeWindowCount : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-p) / (4 * representativeWindowCount) := by
        rw [Real.exp_sub, Real.exp_log hcount]
      _ ≤ 3 * sigma / (4 * representativeWindowCount) :=
        div_le_div_of_nonneg_right (by linarith) hcount.le

theorem exists_polynomial_scored_crt_representative_patch :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (s : ℕ) (hs : 1 ≤ s)
      (f : ZMod (∏ j, N j) → ℝ) {p M sigma : ℝ},
      0 ≤ p → 0 < M → M ≤ Real.exp p → Real.exp (-p) ≤ sigma →
      (∀ x, |f x| ≤ M) → sigma ≤ (𝔼 x, f x) →
      1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M) →
      ∃ w : RepresentativeWindow,
        Real.log (2 + ((w.crtPatch N hN s hs).kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤
          𝔼 u : (j : J) → ZMod (N j), f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_representativeWindow_budget
  refine ⟨C, hC, ?_⟩
  intro J _ _ N _ _ hN s hs f p M sigma hp hM hMexp hsigma hf hscore hsize
  obtain ⟨w, hw, hws⟩ := exists_scored_crt_representative_patch N hN s hs f hM
    (lt_of_lt_of_le (Real.exp_pos _) hsigma) hf hscore hsize
  have hb := hbudget p M sigma hp hM hMexp hsigma
  refine ⟨w, ?_, hb.2.trans hws⟩
  rw [RepresentativeWindow.crtPatch_lip, hw]
  simpa only [add_assoc] using hb.1

end Erdos3

end

end OAI
