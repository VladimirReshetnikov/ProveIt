import OAI.Combinatorics.Progressions.Linear.QuarticKernelCorrelation

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticPairComponent (out : Fin W.outputDim) (v : Fin 4 → Fin 4) :
    W.model.Niltest (fun _ : Fin 4 => 1) :=
  (W.component out).affinePullback
    (fun j a => if a = (if j.1 = 0 then v 0 else if j.2.val = 0 then v 1
      else if j.2.val = 1 then v 2 else v 3) then 1 else 0) (fun _ => 0)

theorem quarticPairComponent_eval (out : Fin W.outputDim) (v : Fin 4 → Fin 4)
    (n : Fin 4 → ℤ) :
    (W.quarticPairComponent out v).eval n =
      W.eval out (quarticInput (n (v 0)) ![n (v 1), n (v 2), n (v 3)]) := by
  rw [quarticPairComponent, Niltest.eval_affinePullback, component_eval]
  apply congrArg (W.eval out)
  funext j
  rcases j with ⟨j, a⟩
  fin_cases j <;> fin_cases a <;>
    simp [integerAffineMap, quarticInput, ite_mul]

theorem quarticPairComponent_complexity (out : Fin W.outputDim) (v : Fin 4 → Fin 4) :
    (W.quarticPairComponent out v).ComplexityLE (p + 4) := W.component_complexity out

theorem quarticPairComponent_vertical (out : Fin W.outputDim) (v : Fin 4 → Fin 4)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : W.model.Space) :
    (W.quarticPairComponent out v).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.quarticPairComponent out v).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

theorem quarticPairComponent_orbit_eq (out out' : Fin W.outputDim) (v : Fin 4 → Fin 4) :
    (W.quarticPairComponent out v).orbit = (W.quarticPairComponent out' v).orbit := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def quarticPairBudget (p q : ℝ) : ℝ := 4 * (p + q + 1) + raisedNiltestBudget (p + q) + 6

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

abbrev QuarticPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def quarticPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : QuarticReplicatedIndex, 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def quarticPairTests :
    ∀ k, (V.quarticPairModels k).Niltest (fun _ : Fin 4 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![W.quarticPairComponent i id,
      (W.quarticPairComponent j ![1, 0, 2, 3]).conjugate] k

noncomputable def quarticPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem quarticPairTests_eval (n : Fin 4 → ℤ) :
    (∏ k, (V.quarticPairTests k).eval n) =
      W.quarticAntisymmetric i j n * star (V.test.eval n) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by decide : 3 ≤ ∑ _ : QuarticReplicatedIndex, 1)).conjugate.eval n *
    ((W.quarticPairComponent i id).eval n *
      (W.quarticPairComponent j ![1, 0, 2, 3]).conjugate.eval n) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.quarticPairComponent_eval, W.quarticPairComponent_eval]
  have h0 : (![1, 0, 2, 3] : Fin 4 → Fin 4) 0 = 1 := rfl
  have h1 : (![1, 0, 2, 3] : Fin 4 → Fin 4) 1 = 0 := rfl
  have h2 : (![1, 0, 2, 3] : Fin 4 → Fin 4) 2 = 2 := rfl
  have h3 : (![1, 0, 2, 3] : Fin 4 → Fin 4) 3 = 3 := rfl
  simp only [id_eq, h0, h1, h2, h3, NativeMultidegreeNilcharacter.quarticAntisymmetric]
  ring

theorem quarticPairTests_vertical (k : Option (Fin 2))
    (z : (V.quarticPairModels k).RealGroup)
    (hz : z ∈ (V.quarticPairModels k).filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : (V.quarticPairModels k).Space) :
    (V.quarticPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.quarticPairFrequencies k) z.coord : ℝ) : CircleFourier.Circle) *
          (V.quarticPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by decide : 3 < ∑ _ : QuarticReplicatedIndex, 1) z hz x
  | some k =>
    fin_cases k
    · exact W.quarticPairComponent_vertical i id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.quarticPairComponent_vertical j ![1, 0, 2, 3]) z hz x

include V in
theorem quarticPairBudget_six_le : 6 ≤ quarticPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold quarticPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem quarticPairTests_complexity (k : Option (Fin 2)) :
    (V.quarticPairTests k).ComplexityLE (quarticPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by decide) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold quarticPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ quarticPairBudget p q := by
      unfold quarticPairBudget
      linarith
    fin_cases k
    · exact (W.quarticPairComponent_complexity i id).mono hcost
    · exact (W.quarticPairComponent_complexity j ![1, 0, 2, 3]).mono hcost

end NativeSampleCorrelation
end Erdos3

end

end OAI
