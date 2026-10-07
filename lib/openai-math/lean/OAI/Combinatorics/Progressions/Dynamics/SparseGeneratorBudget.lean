import OAI.Combinatorics.Progressions.Estimates.BoundedSparseGenerators
import OAI.Combinatorics.Progressions.Estimates.RationalImageIntersections

namespace OAI

section

namespace Erdos3

noncomputable def sparseGeneratorBudget (p : ℝ) : ℝ := p + p * ((p + 2) ^ 7 + p)

theorem sparseGeneratorBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ sparseGeneratorBudget p := by
  unfold sparseGeneratorBudget
  positivity

theorem sparseGeneratorHeight_bound {p : ℝ} (hp : 0 ≤ p) (r n H : ℕ)
    (hr : (r : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (((n + 1) * (rationalKernelHeight r H * H) ^ n : ℕ) : ℝ) ≤
      Real.exp (sparseGeneratorBudget p) := by
  have hfront : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn le_rfl).trans (Real.add_one_le_exp p)
  have hbase : (rationalKernelHeight r H : ℝ) * H ≤ Real.exp ((p + 2) ^ 7 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul (rationalKernelHeight_le_budget r H hp hr hH) hH
      (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ (rationalKernelHeight r H : ℝ) * H) hbase n
  rw [← Real.exp_nat_mul] at hpower
  push_cast
  calc
    ((n : ℝ) + 1) * ((rationalKernelHeight r H : ℝ) * H) ^ n ≤
        Real.exp p * Real.exp ((n : ℝ) * ((p + 2) ^ 7 + p)) :=
      mul_le_mul hfront hpower (by positivity) (Real.exp_pos _).le
    _ = Real.exp (p + (n : ℝ) * ((p + 2) ^ 7 + p)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (sparseGeneratorBudget p) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hn (by positivity))

theorem exists_sparse_generators_exp_height
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H : ℕ} (hH : 1 ≤ H) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : ℝ) ≤ Real.exp (sparseGeneratorBudget p) ∧
      ∃ w : κ → ι → ℚ, Submodule.span ℚ (Set.range w) = fourSparseFirstProjection J K ∧
        ∀ a i, RationalHeightLE (w a i) M := by
  obtain ⟨r, hr, w, hw, hwH⟩ := exists_bounded_sparse_generators J K v hv hH hvH
  refine ⟨(Fintype.card κ + 1) * (rationalKernelHeight r H * H) ^ Fintype.card κ, ?_,
    sparseGeneratorHeight_bound hp r (Fintype.card κ) H
      ((Nat.cast_le.mpr hr).trans hrows) hcols hHp, w, hw, hwH⟩
  have hkernel := rationalKernelHeight_pos r hH
  exact Nat.mul_pos (Nat.zero_lt_succ _) (pow_pos (Nat.mul_pos hkernel hH) _)

end Erdos3

end

end OAI
