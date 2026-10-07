import OAI.Combinatorics.Progressions.Estimates.SourceUnitCover

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeDegreeRankFamily (s r : ℕ) (A : Type*) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  rank : model.DegreeRankStructure r
  complexity : rank.ComplexityLE p
  orbit : A → model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)
  normalized : ∀ a, model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (orbit a) = 1
  outputDim : ℕ
  output_pos : 0 < outputDim
  output_bound : (outputDim : ℝ) ≤ Real.exp p
  vertical : model.UnitVerticalObservable (rank.realSubgroup s r) (Fin outputDim) p

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

namespace NativeDegreeRankFamily

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def eval (i : Fin W.outputDim) (a : A) (n : ℤ) : ℂ :=
  W.vertical.observable i (QuotientGroup.mk
    (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => n) (W.orbit a)))

noncomputable def evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) : ℂ :=
  W.eval i a (n.val : ℤ)

theorem unit_eval (a : A) (n : ℤ) : ∑ i, ‖W.eval i a n‖ ^ 2 = 1 := W.vertical.unit _

theorem norm_eval (i : Fin W.outputDim) (a : A) (n : ℤ) : ‖W.eval i a n‖ ≤ 1 := W.vertical.norm i _

theorem orbit_rank_normalized (a : A) :
    W.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) 0
      (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a)) = 1 := by
  rw [W.rank.orbitEquiv_eval]
  exact W.normalized a

noncomputable def mono (hpq : p ≤ q) : NativeDegreeRankFamily s r A q :=
  { W with
    complexity := W.complexity.mono W.rank hpq
    output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
    vertical := W.vertical.mono hpq }

theorem mono_eval (hpq : p ≤ q) (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.mono hpq).eval i a n = W.eval i a n := rfl

end NativeDegreeRankFamily

end Erdos3

end

end OAI
