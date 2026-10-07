import OAI.Combinatorics.Progressions.Estimates.RealGeneratorCombinations
import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem exists_controlled_coordinate_lifts
    {μ ι κ σ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hφH : ∀ j i, RationalHeightLE (φ (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a q : ι → ℝ),
        a + q ∈ realRationalCoordinateSpan (U.map φ) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] V, E ∈ U.baseChange ℝ ∧ Q ∈ U.baseChange ℝ ∧
          realRationalCoordinateEquiv (φ.baseChange ℝ E) = a ∧
          realRationalCoordinateEquiv (φ.baseChange ℝ Q) = q ∧
          ‖(b.baseChange ℝ).equivFun E‖ ≤
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m := by
  let A : Matrix ι κ ℚ := fun i j => φ (v j) i
  let B : Matrix μ κ ℚ := fun i j => b.repr (v j) i
  have hvφ : Submodule.span ℚ (Set.range (fun j => φ (v j))) = U.map φ := by
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan := realRationalCoordinateSpan_eq_image (U.map φ) (fun j => φ (v j)) hvφ
  have hvU (j : κ) : v j ∈ U := hv ▸ Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting A hH hl
    (fun i j => hφH j i) hp hι hκ hHp hlp T hT
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) := hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator B : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power B hp 1 hμ hκ
      (fun i j => (Nat.cast_le.mpr (hvH j i).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (x : κ → ℝ) :
      ‖(fun i j => (B i j : ℝ)) *ᵥ x‖ ≤ Real.exp ((p + 2) ^ 3) * ‖x‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hvH j i).abs_real_le) x).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg x))
  have hBm : 0 < matrixDenominator B * m := Nat.mul_pos (matrixDenominator_pos B) hm
  have hBmp : ((matrixDenominator B * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  refine ⟨l * (matrixDenominator B * m), Nat.mul_pos hl hBm, ?_, dvd_mul_right _ _, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hBmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  · intro α hα a q hsum ha hq
    rw [hspan] at hsum
    obtain ⟨x, hx⟩ := hsum
    obtain ⟨hSa, hSq, hslow, hgrid, _⟩ := hsolve α hα a q x ha hq hx
    let ca := (fun i j => (S i j : ℝ)) *ᵥ a
    let cq := (fun i j => (S i j : ℝ)) *ᵥ q
    refine ⟨realGeneratorCombination v ca, realGeneratorCombination v cq,
      realGeneratorCombination_mem U v hvU ca, realGeneratorCombination_mem U v hvU cq,
      ?_, ?_, ?_, ?_⟩
    · rw [realGeneratorCombination_map_coordinates]
      exact hSa
    · rw [realGeneratorCombination_map_coordinates]
      exact hSq
    · rw [realGeneratorCombination_coordinates]
      calc
        ‖(fun i j => (b.repr (v j) i : ℝ)) *ᵥ ca‖ ≤ Real.exp ((p + 2) ^ 3) * ‖ca‖ := hnorm ca
        _ ≤ Real.exp ((p + 2) ^ 3) * (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left hslow (Real.exp_pos _).le
        _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]; congr 2; ring
    · rw [realGeneratorCombination_coordinates]
      exact realDenominatorGrid_subset_of_dvd hBm (dvd_mul_left _ _)
        (real_matrix_denominator_grid B m cq hgrid)

end Erdos3

end

end OAI
