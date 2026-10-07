import OAI.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_frozen_affine_expansion {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (A b : σ → ℤ) (k : Fin W.outputDim),
      (∀ i, i ∉ S → A i = 0) →
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (∑ i ∈ S, bound i) ((p + C) ^ C)
          (fun x => W.eval k (fun i => b i + A i * x ())), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest bound
  refine ⟨C, hC, ?_⟩
  intro p W S A b k hA
  classical
  obtain ⟨t, n, ht, _, D, hD⟩ := hfreeze W S b k
  subst t
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _, hT, _, heval⟩ := hD
  let U := T.affinePullback (fun i (_ : Unit) => A i.val) (fun i => b i.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = W.eval k (fun i => b i + A i * x ()) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · simp [freezeCoordinates, hi, integerAffineMap]
    · simp [freezeCoordinates, hi, hA i hi]
  exact ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
