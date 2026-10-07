/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis

namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

noncomputable def testingNiltest (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) : B.model.Niltest (fun _ : Fin 1 => 1) := by
  classical
  exact if hk.1 ∈ B.shifts then
    (B.mode hk.1 hk.2).linearPullbackHom (fun _ : Unit =>
      { toFun := fun x => x 0, map_zero' := rfl, map_add' := fun _ _ => rfl })
  else RationalFilteredNilmanifold.Niltest.const B.model (fun _ : Fin 1 => 1) 0

theorem testingNiltest_eval (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) (x : ZMod N) :
    (B.testingNiltest hk).eval (fun _ => (x.val : ℤ)) = B.testingFamily hk x := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · simp only [testingNiltest, testingFamily, ite_eq_left hh,
      RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom,
      RationalFilteredNilmanifold.Niltest.evalCyclic,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  · simp only [testingNiltest, testingFamily, ite_eq_right hh,
      RationalFilteredNilmanifold.Niltest.eval_const]

theorem testingNiltest_norm (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) : (B.testingNiltest hk).normBound ≤ 1 := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · simp only [testingNiltest, ite_eq_left hh]
    change (B.mode hk.1 hk.2).normBound ≤ 1
    exact B.mode_norm hk.1 hh hk.2
  · simp [testingNiltest, hh, RationalFilteredNilmanifold.Niltest.const]

theorem testingNiltest_complexity (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) : (B.testingNiltest hk).ComplexityLE (q + 2) := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · simp only [testingNiltest, ite_eq_left hh,
      RationalFilteredNilmanifold.Niltest.linearPullbackHom_complexityLE]
    exact (B.mode_complexity hk.1 hh hk.2).mono (by linarith)
  · simp only [testingNiltest, ite_eq_right hh]
    refine ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono B.model B.geometry
      (by linarith), ?_⟩
    change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ q + 2
    simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
    have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

end Erdos3.PositiveShiftBasis

end

end OAI
