import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_topInvariant_reconstruction_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (Q : RationalFilteredNilmanifold M s n) {w : σ → ℕ}
      (T : D.Niltest w) (S : Q.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      S.normBound = T.normBound →
      S.lipBound = rationalReconstructionLipschitzBound s d n ⌈Real.exp p⌉₊
        T.lipBound T.normBound →
      S.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 1 + Polynomial.C a) ^ a + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d n D Q w T S p hp hT hQ hSn hSl
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n ⌈Real.exp p⌉₊ T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by
        linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + C) ^ C := by
    simpa [r, P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
