import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T U : D.Niltest w) (hT : ∀ x, ‖T.observable x‖ ≤ 1)
  (hU : ∀ x, ‖U.observable x‖ ≤ 1)

noncomputable def unitComparison : D.Niltest w where
  orbit := T.orbit
  observable x := T.observable x * star (U.observable x)
  normBound := 1
  lipBound := U.lipBound + T.lipBound
  norm_le x := by
    change ‖T.observable x * star (U.observable x)‖ ≤ (1 : ℝ)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hT x)).trans (hU x)
  lipschitz := by
    let := D.metricSpace
    simpa only [one_mul] using lipschitz_mul_star_of_bounds T.observable U.observable
      (Bf := 1) (Bg := 1) T.lipschitz U.lipschitz hT hU

theorem unitComparison_eval (horbit : T.orbit = U.orbit) (x : σ → ℤ) :
    (T.unitComparison U hT hU).eval x = T.eval x * star (U.eval x) := by
  change T.eval x * star (U.observable (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w x T.orbit))) = _
  rw [horbit]
  rfl

theorem unitComparison_complexity {p : ℝ}
    (hTc : T.ComplexityLE p) (hUc : U.ComplexityLE p) :
    (T.unitComparison U hT hU).ComplexityLE (p + 4) := by
  refine ⟨hTc.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + ((U.lipBound + T.lipBound : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have hT' := T.observable_budget hTc
  have hU' := U.observable_budget hUc
  calc
    _ ≤ 5 * Real.exp p := by
      simp only [NNReal.coe_add]
      linarith [T.normBound.coe_nonneg, U.normBound.coe_nonneg, Real.exp_nonneg p]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p + 4) := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
