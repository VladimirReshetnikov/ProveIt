import OAI.Combinatorics.Progressions.Estimates.CommonPositivePartitionRefinement
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom

namespace OAI

section

universe u

namespace Erdos3.PositiveCyclicModel

open scoped TensorProduct

attribute [local instance] PositiveCyclicModel.lie PositiveCyclicModel.algebra
  PositiveCyclicModel.topology PositiveCyclicModel.topologicalAdd
  PositiveCyclicModel.continuousSMul PositiveCyclicModel.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
  (R : PositiveCyclicModel.{u} s N p f) {σ : Type*} [Fintype σ]

noncomputable def coordinateTest (i : σ) : R.model.Niltest (fun _ : σ => 1) :=
  R.test.linearPullbackHom (fun _ : Unit =>
    { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl })

theorem coordinateTest_eval (i : σ) (x : σ → ℤ) :
    (R.coordinateTest i).eval x = R.test.eval (fun _ => x i) := by
  exact R.test.eval_linearPullbackHom _ x

theorem coordinateTest_complexity (i : σ) :
    (R.coordinateTest i).ComplexityLE p := R.complexity

theorem coordinateTest_evalCyclic (i : σ) (x : σ → ZMod N) :
    (R.coordinateTest i).evalCyclic N x = (f (x i) : ℂ) := by
  change (R.coordinateTest i).eval (fun j => ((x j).val : ℤ)) = _
  rw [R.coordinateTest_eval]
  apply Complex.ext
  · exact (R.eval (x i)).symm
  · simpa only [Complex.ofReal_im] using
      (R.test.unit_interval_eval R.positive (fun _ => ((x i).val : ℤ))).1

end Erdos3.PositiveCyclicModel

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] PositiveCyclicModel.lie PositiveCyclicModel.algebra
  PositiveCyclicModel.topology PositiveCyclicModel.topologicalAdd
  PositiveCyclicModel.continuousSMul PositiveCyclicModel.hausdorff

theorem exists_positive_coordinate_product {σ : Type} [Fintype σ]
    {s N : ℕ} [NeZero N] {p : ℝ} {f : σ → ZMod N → ℝ}
    (hp : 0 ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hf : ∀ i, PositiveCyclicNiltest.{0} s N p (f i)) :
    ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s
        (productNiltestBudget (raisedNiltestBudget p)) g) ∧
      ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) = ∏ i, (f i (x i) : ℂ) := by
  classical
  let R := fun i => Classical.choice ((hf i).model_nonempty hp)
  let D := fun i => (R i).model
  let T := fun i => (R i).coordinateTest i
  let : FiniteDimensional ℚ (∀ i, (R i).L) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, (R i).L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, (R i).L)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, (R i).L)) := realification_moduleTopology_t2 (productFinBasis D)
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hσ' : (Fintype.card σ : ℝ) ≤ raisedNiltestBudget p := hσ.trans (le_raisedNiltestBudget p)
  have hT : ∀ i, (T i).ComplexityLE (raisedNiltestBudget p) :=
    fun i => (R i).coordinateTest_complexity i
  let S := piNiltest D T hp' hσ' hT
  refine ⟨S.eval, ⟨NativeIntegerExpansion.ofTest S
    (piNiltest_complexity D T hp' hσ' hT) (fun _ => rfl)⟩, ?_⟩
  intro x
  change (piNiltest D T hp' hσ' hT).eval _ = _
  rw [piNiltest_eval]
  apply Finset.prod_congr rfl
  intro i _
  exact (R i).coordinateTest_evalCyclic i x

end Erdos3

end

end OAI
