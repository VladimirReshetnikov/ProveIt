import OAI.Combinatorics.Progressions.Estimates.SourceUnitCover

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ τ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def component (i : Fin W.outputDim) : W.model.Niltest (fun _ : σ => 1) where
  orbit := W.multi.orbitToOrdinary W.orbit
  observable := W.vertical.observable i
  normBound := 1
  lipBound := W.vertical.lipBound
  norm_le := W.vertical.norm i
  lipschitz := W.vertical.lipschitz i

theorem component_eval (i : Fin W.outputDim) (x : σ → ℤ) : (W.component i).eval x = W.eval i x := by
  exact congrArg (fun z : W.model.RealGroup => W.vertical.observable i (QuotientGroup.mk z))
    (W.multi.orbitToOrdinary_eval W.orbit x)

theorem component_complexity (i : Fin W.outputDim) : (W.component i).ComplexityLE (p + 4) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  refine ⟨W.complexity.1.mono W.model (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (W.vertical.lipBound : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp p := by linarith [W.vertical.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem exists_affine_niltest [Fintype τ] (i : Fin W.outputDim) (A : σ → τ → ℤ) (b : σ → ℤ) :
    ∃ T : W.model.Niltest (fun _ : τ => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ x, T.eval x = W.eval i (integerAffineMap A b x) := by
  refine ⟨(W.component i).affinePullback A b, rfl, W.component_complexity i, ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, W.component_eval]

theorem exists_linear_niltest [Fintype τ] (i : Fin W.outputDim) (f : σ → ((τ → ℤ) →+ ℤ)) :
    ∃ T : W.model.Niltest (fun _ : τ => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ x, T.eval x = W.eval i (fun j => f j x) := by
  refine ⟨(W.component i).linearPullbackHom f, rfl, W.component_complexity i, ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, W.component_eval]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
