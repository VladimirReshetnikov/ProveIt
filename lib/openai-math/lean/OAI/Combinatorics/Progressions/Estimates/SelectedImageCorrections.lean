import OAI.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection

namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_selected_image_corrections
    {η ι κ σ : Type*} [Fintype η] [Fintype ι] [Fintype κ]
    (A : Matrix η κ ℚ) (ρ : ι → η) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ), 0 < m ∧
      (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b : ι → ℝ) (x : η → ℝ),
        x ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
        (∀ i, x (ρ i) = a i + b i) →
        let e := (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a)
        let q := (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b)
        e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        (∀ i, e (ρ i) = a i) ∧ (∀ i, q (ρ i) = b i) ∧
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
        q ∈ realDenominatorGrid m ∧
        x - e - q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) ∧
        ∀ i, (x - e - q) (ρ i) = 0 := by
  let C : Matrix ι κ ℚ := fun i j => A (ρ i) j
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting C hH hl
    (fun i j => hA (ρ i) j) hp hι hκ hHp hlp T hT
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power A hp 1 hη hκ
      (fun i j => (Nat.cast_le.mpr (hA i j).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (y : κ → ℝ) :
      ‖(fun i j => (A i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hA i j).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨S, matrixDenominator A * m, Nat.mul_pos (matrixDenominator_pos A) hm, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro α hα a b x hx ha hb hselect e q
    obtain ⟨z, hz⟩ := hx
    have hC : (fun i j => (C i j : ℝ)) *ᵥ z = a + b := by
      funext i
      exact (congrFun hz (ρ i)).trans (hselect i)
    obtain ⟨hSa, hSb, hslow, hgrid, _⟩ := hsolve α hα a b z ha hb hC
    have he : e ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) :=
      ⟨(fun i j => (S i j : ℝ)) *ᵥ a, rfl⟩
    have hq : q ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) :=
      ⟨(fun i j => (S i j : ℝ)) *ᵥ b, rfl⟩
    have heq (i : ι) : e (ρ i) = a i := congrFun hSa i
    have hqq (i : ι) : q (ρ i) = b i := congrFun hSb i
    refine ⟨he, hq, heq, hqq, ?_, real_matrix_denominator_grid A m _ hgrid,
      Submodule.sub_mem _ (Submodule.sub_mem _ ⟨z, hz⟩ he) hq, ?_⟩
    · calc
        ‖e‖ ≤ Real.exp ((p + 2) ^ 3) * ‖(fun i j => (S i j : ℝ)) *ᵥ a‖ := hnorm _
        _ ≤ Real.exp ((p + 2) ^ 3) *
            (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left hslow (Real.exp_pos _).le
        _ = _ := by
          rw [← mul_div_assoc, ← Real.exp_add]
          congr 2
          ring
    · intro i
      change x (ρ i) - e (ρ i) - q (ρ i) = 0
      rw [hselect i, heq i, hqq i]
      ring

end Erdos3

end

end OAI
