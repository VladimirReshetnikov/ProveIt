import OAI.Combinatorics.Progressions.Estimates.SelectedImageCorrections
import OAI.Combinatorics.Progressions.Linear.RealSparseFourProjection

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_sparse_coordinate_corrections
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (K : Finset (Fin 4))
    (v : κ → Fin 4 → ι → ℚ) (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hK : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 →
      ∀ (a b : (Σ _ : K, ι) → ℝ) (x : (Σ _ : Fin 4, ι) → ℝ),
        x ∈ realFourCoordinateSpan J →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        (∀ j : Σ _ : K, ι, x ⟨j.1, j.2⟩ = a j + b j) →
        ∃ e q : (Σ _ : Fin 4, ι) → ℝ,
          e ∈ realFourCoordinateSpan J ∧ q ∈ realFourCoordinateSpan J ∧
          (∀ j : Σ _ : K, ι, e ⟨j.1, j.2⟩ = a j) ∧
          (∀ j : Σ _ : K, ι, q ⟨j.1, j.2⟩ = b j) ∧
          ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          q ∈ realDenominatorGrid m ∧
          x - e - q ∈ realFourCoordinateSpan J ∧
          (fun i => (x - e - q) ⟨0, i⟩) ∈
            realRationalCoordinateSpan (fourSparseFirstProjection J K) := by
  let A : Matrix (Σ _ : Fin 4, ι) κ ℚ := fun j a => v a j.1 j.2
  let ρ : (Σ _ : K, ι) → (Σ _ : Fin 4, ι) := fun j => ⟨j.1, j.2⟩
  have hspan : realFourCoordinateSpan J =
      LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
    ext x
    rw [← hv, realFourCoordinateSpan_span]
    exact real_column_span_mem_iff A x
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_selected_image_corrections A ρ hH hl
    (fun i a => hvH a i.1 i.2) hp hι hK hκ hHp hlp T hT
  refine ⟨m, hm, hmp, ?_⟩
  intro α hα a b x hx ha hb hselect
  obtain ⟨he, hq, heq, hqq, hslow, hgrid, hrem, hzero⟩ :=
    hsolve α hα a b x (hspan ▸ hx) ha hb hselect
  refine ⟨_, _, hspan.symm ▸ he, hspan.symm ▸ hq, heq, hqq, hslow, hgrid,
    hspan.symm ▸ hrem, ?_⟩
  apply mem_realSparseFirstProjection_of_zero J K _ (hspan.symm ▸ hrem)
  intro k hk i
  exact hzero ⟨⟨k, hk⟩, i⟩

end Erdos3

end

end OAI
