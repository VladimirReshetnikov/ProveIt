import OAI.Combinatorics.Progressions.Dynamics.SparseGeneratorBudget
import OAI.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
import OAI.Combinatorics.Progressions.Linear.RealSparseFourProjection

namespace OAI

section

namespace Erdos3

theorem exists_coordinate_intersection_corrections
    {ι κ ν σ : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (U V : Submodule ℚ (ι → ℚ)) (v : κ → ι → ℚ) (w : ν → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = U) (hw : Submodule.span ℚ (Set.range w) = V)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a i, RationalHeightLE (v a i) H) (hwH : ∀ a i, RationalHeightLE (w a i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ realRationalCoordinateSpan U →
        β - e₂ - q₂ ∈ realRationalCoordinateSpan V →
        ‖e₁‖ ≤ Real.exp p / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp p / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ realRationalCoordinateSpan (U ⊓ V) := by
  simpa only [realRationalCoordinateSpan_inf, realRationalCoordinateSpan_eq_image U v hv,
    realRationalCoordinateSpan_eq_image V w hw] using
    exists_common_intersection_corrections (fun i a => v a i) (fun i a => w a i)
      hH hl (fun i a => hvH a i) (fun i a => hwH a i) hp hι hcols hHp hlp T hT

end Erdos3

end

section

namespace Erdos3

theorem exists_dependent_coordinate_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (h₁₂ : (Fintype.card (Σ _ : ({1, 2} : Finset (Fin 4)), ι) : ℝ) ≤ p)
    (h₁₃ : (Fintype.card (Σ _ : ({1, 3} : Finset (Fin 4)), ι) : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ κ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ)
    (hT : ∀ i, Real.exp (separationBudget (p + sparseGeneratorBudget p)) ≤ T i) :
    let P := p + sparseGeneratorBudget p
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β e₁ e₂ q₁ q₂ : ι → ℝ),
        β - e₁ - q₁ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) →
        β - e₂ - q₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) →
        ‖e₁‖ ≤ Real.exp P / monomialScale T α →
        ‖e₂ - e₁‖ ≤ Real.exp P / monomialScale T α →
        q₁ ∈ realDenominatorGrid l → q₂ ∈ realDenominatorGrid l →
        ∃ e q : ι → ℝ,
          ‖e‖ ≤ (Real.exp P + Real.exp ((P + 2) ^ 3 + (P + 2) ^ 18 + P)) /
            monomialScale T α ∧ q ∈ realDenominatorGrid m ∧
          β - e - q ∈ realRationalCoordinateSpan (fourDependentProjection J) := by
  intro P
  have hκ : (Fintype.card κ : ℝ) ≤ p := by
    rw [Fintype.card_sum, Nat.cast_add] at hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
  have hpP : p ≤ P := le_add_of_nonneg_right (sparseGeneratorBudget_nonneg hp)
  have hP : 0 ≤ P := hp.trans hpP
  obtain ⟨M₁, hM₁, hM₁p, w₁, hw₁, hw₁H⟩ :=
    exists_sparse_generators_exp_height J {1, 2} v hv hH hvH hp h₁₂ hκ hHp
  obtain ⟨M₂, hM₂, hM₂p, w₂, hw₂, hw₂H⟩ :=
    exists_sparse_generators_exp_height J {1, 3} v hv hH hvH hp h₁₃ hκ hHp
  have hMP : ((max M₁ M₂ : ℕ) : ℝ) ≤ Real.exp P := by
    rw [Nat.cast_max]
    apply (max_le hM₁p hM₂p).trans
    apply Real.exp_le_exp.mpr
    exact le_add_of_nonneg_left hp
  exact exists_coordinate_intersection_corrections
    (fourSparseFirstProjection J {1, 2}) (fourSparseFirstProjection J {1, 3})
    w₁ w₂ hw₁ hw₂ (hM₁.trans (le_max_left _ _)) hl
    (fun a i => (hw₁H a i).mono (le_max_left _ _))
    (fun a i => (hw₂H a i).mono (le_max_right _ _))
    hP (hι.trans hpP) (hcols.trans hpP) hMP
    (hlp.trans (Real.exp_le_exp.mpr hpP)) T hT

end Erdos3

end

end OAI
