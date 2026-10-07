import OAI.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem residue_pair_discrepancy_step_zero {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K 0 e) (T : V.Niltest (fun _ : σ => 1))
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ)
    (hbase : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u))
    (hfine : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v)) :
    ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ = 0 := by
  let := hbase
  let := hfine
  rw [residuePairMean_false, residuePairMean_true]
  simp only [residueBoxStrideValue, RationalFilteredNilmanifold.Niltest.eval_step_zero,
    Fintype.expect_const, sub_self, norm_zero]

theorem not_anchored_child_comparison_step_zero {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K 0 e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost η δ : ℝ) (hη : 0 < η) (lo : σ → ℤ) (N : σ → ℕ)
    (M P : ℕ) (u v : σ → ℤ) (J : σ → ℕ) :
    ¬ AnchoredChildResidueComparison V child cost η δ lo N M P u v J := by
  rintro ⟨lo', N', w, z, U, _, _, _, _, _, _, _, _, hbase, hfine, _, _, _, hgap⟩
  have hzero := residue_pair_discrepancy_step_zero V U lo' N' (Nat.lcm M (M * P)) w z J hbase hfine
  rw [hzero] at hgap
  linarith

end Erdos3

end

end OAI
