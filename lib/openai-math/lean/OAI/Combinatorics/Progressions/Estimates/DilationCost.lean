import OAI.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
import OAI.Combinatorics.Progressions.Dynamics.DilationBudgets
import OAI.Combinatorics.Progressions.Dynamics.MultilinearityBudgets

namespace OAI

section

namespace Erdos3.MultilinearityBudget

open scoped TensorProduct NNReal

noncomputable def reconstructionExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_rationalReconstructionLipschitzBound_exp s)

theorem reconstructionExponent_ge_two (s : ℕ) : 2 ≤ reconstructionExponent s :=
  (Classical.choose_spec (exists_rationalReconstructionLipschitzBound_exp s)).1

theorem reconstructionExponent_control (s d n H : ℕ) (A B : ℝ≥0) (p : ℝ)
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hA : (A : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    (rationalReconstructionLipschitzBound s d n H A B : ℝ) ≤
      Real.exp ((p + reconstructionExponent s) ^ reconstructionExponent s) :=
  (Classical.choose_spec (exists_rationalReconstructionLipschitzBound_exp s)).2 d n H A B p
    hp hd hn hH hA hB

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (C d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE (quotient p))
    (hd : (d : ℝ) ≤ reconstruction C p) (hH : (H : ℝ) ≤ Real.exp (reconstruction C p))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction C p))
    (hnorm : T.normBound = 1) (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total C (reconstructionExponent s) p) := by
  have hR := reconstruction_bounds C hp
  have hQle : quotient p ≤ reconstruction C p :=
    (le_add_of_nonneg_right zero_le_one).trans hR.2.2.1
  have hTlip : (T.lipBound : ℝ) ≤
      Real.exp ((reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s) := by
    rw [hlip]
    exact reconstructionExponent_control s d n H A 1 _ hR.1 hd (hQ.1.trans hQle) hH hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds C (reconstructionExponent s) hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds C (reconstructionExponent s) hp).2

end Erdos3.MultilinearityBudget

end

section

namespace Erdos3.DilationBudget

open scoped TensorProduct NNReal

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (t : ℕ) (q : ℤ) (d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (p + 1))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction t q p))
    (hnorm : T.normBound = 1)
    (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total t q (MultilinearityBudget.reconstructionExponent s) p) := by
  have hR := reconstruction_bounds t q hp
  have hpR : p ≤ reconstruction t q p := (by linarith : p ≤ p + 1).trans hR.2
  have hTlip : (T.lipBound : ℝ) ≤ Real.exp
      ((reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s) := by
    rw [hlip]
    exact MultilinearityBudget.reconstructionExponent_control s d n H A 1 _ hR.1
      (hd.trans hpR) (hQ.1.trans hpR) (hH.trans (Real.exp_le_exp.mpr hR.2)) hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
      MultilinearityBudget.reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds t q _ hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds t q _ hp).2

end Erdos3.DilationBudget

end

end OAI
