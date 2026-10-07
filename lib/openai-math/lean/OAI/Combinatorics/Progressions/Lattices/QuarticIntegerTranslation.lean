import OAI.Combinatorics.Progressions.Estimates.QuarticSurvivorMultilinearization

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quartic_integer_translation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (a b : QuarticReplicatedIndex → ℤ),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    UnitVerticalObservable.exists_integer_translation_equivalence_budget 3
  refine ⟨C, hC, ?_⟩
  intro p W a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let U : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model U (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hI a b
  have heval (i : Fin W.outputDim) (x : QuarticReplicatedIndex → ℤ) :
      U.observable i (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (W.multi.orbitToOrdinary W.orbit))) = W.eval i x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have hl : (fun i x => U.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (x + a)
        (W.multi.orbitToOrdinary W.orbit)))) = (fun i x => W.eval i (x + a)) := by
    funext i x
    exact heval i (x + a)
  have hr : (fun i x => U.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (x + b)
        (W.multi.orbitToOrdinary W.orbit)))) = (fun i x => W.eval i (x + b)) := by
    funext i x
    exact heval i (x + b)
  exact (congrArg₂ (fun f g : Fin W.outputDim → (QuarticReplicatedIndex → ℤ) → ℂ =>
    NativeIntegerVectorEquivalence 3 ((p + C) ^ C) f g) hl hr).mp E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
