import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget
import OAI.Combinatorics.Progressions.Lattices.CircleResiduePartition

namespace OAI

section

namespace Erdos3.RationalTorus

open CircleFourier
open scoped TensorProduct NNReal

theorem residueObservable_lipschitz {q : ℕ} [NeZero q] (j : ZMod q) :
    LipschitzWith (q : ℝ≥0) (fun v : Fin 1 → CircleFourier.Circle => residueCutoff j (v 0)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact ((residueCutoff_lipschitz j).dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist v w 0) (Nat.cast_nonneg q))

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra 1)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra 1)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra 1)] [T2Space (ℝ ⊗[ℚ] Algebra 1)]

noncomputable def residueNiltest {q : ℕ} [NeZero q] (j : ZMod q) :
    (nilmanifold 1).Niltest (fun _ : Unit => 1) :=
  realAffineNiltest (Equiv.refl (Fin 1)) (fun v => residueCutoff j (v 0))
    (fun _ => 0) (fun _ => 1 / (q : ℝ)) (q : ℝ≥0)
    (fun v => residueCutoff_unit_interval j (v 0)) (residueObservable_lipschitz j)

theorem residueNiltest_unit_interval {q : ℕ} [NeZero q] (j : ZMod q) :
    (residueNiltest j).UnitIntervalValued := by
  unfold residueNiltest
  apply realAffineNiltest_unitInterval

theorem residueNiltest_complexity {q : ℕ} [NeZero q] (j : ZMod q) {p : ℝ}
    (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    (residueNiltest j).ComplexityLE (p + 2) := by
  unfold residueNiltest
  apply realAffineNiltest_complexity _ _ _ _ _ _ _ (by linarith) (by norm_num; linarith)
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have h1 := Real.one_le_exp hp
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  change 3 + (q : ℝ) ≤ Real.exp p * Real.exp 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg p)]

theorem residueNiltest_evalCyclic {q : ℕ} [NeZero q] (j : ZMod q)
    (N : ℕ) [NeZero N] (x : ZMod N) :
    (residueNiltest j).evalCyclic N (fun _ : Unit => x) =
      if (x.val : ZMod q) = j then 1 else 0 := by
  classical
  unfold residueNiltest
  rw [realAffineNiltest_evalCyclic]
  simp only [zero_add, mul_one_div]
  rw [← ZMod.toAddCircle_natCast, residueCutoff_at_grid]
  split_ifs <;> rfl

theorem sum_residueNiltest_evalCyclic {q : ℕ} [NeZero q]
    (N : ℕ) [NeZero N] (x : ZMod N) :
    ∑ j : ZMod q, ((residueNiltest j).evalCyclic N (fun _ : Unit => x)).re = 1 := by
  classical
  simp [residueNiltest_evalCyclic, apply_ite]

theorem residueNiltest_positive_iff {q : ℕ} [NeZero q] (j : ZMod q)
    (N : ℕ) [NeZero N] (x : ZMod N) :
    0 < ((residueNiltest j).evalCyclic N (fun _ : Unit => x)).re ↔ (x.val : ZMod q) = j := by
  classical
  rw [residueNiltest_evalCyclic]
  split_ifs <;> simp_all

end Erdos3.RationalTorus

end

end OAI
