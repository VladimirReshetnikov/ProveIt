import OAI.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
import OAI.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_free_top_frequency
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (x : SubspaceFreeLift.Algebra S r),
      x ∈ (SubspaceFreeLift.filtration S T.filtration.rank_le_degree).layer s r →
      pairDifferenceFunctional V.frequency
        (SubspaceFreeLift.evaluation S J
          (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS x) = 0 := by
  intro S hS J x hx
  apply FreeDegreeRankLieAlgebra.lift_top_frequency_zero
    (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration
    (SubspaceFreeLift.weight S) (SubspaceFreeLift.weight_pos S)
    (fun a => (J a.1 a.2).val) (fun a => hS a.1 (J a.1 a.2).property)
    (pairDifferenceFunctional V.frequency) _ hx
  intro a hd hr
  classical
  let e := Fintype.equivFin (SubspaceFreeLift.Alphabet S)
  let d : Fin (Fintype.card (SubspaceFreeLift.Alphabet S)) → Fin s := fun i => (e.symm i).1
  let z : Fin (Fintype.card (SubspaceFreeLift.Alphabet S)) → Fin 2 → D.CoefficientFreeLieAlgebra :=
    fun i => (J (e.symm i).1 (e.symm i).2).val
  have hd' : lieTreeWeight (fun i => (d i).val + 1) (FreeMagma.map e a) = s := by
    have heq : (fun i => (d i).val + 1) ∘ e = SubspaceFreeLift.weight S := by
      funext i
      change (e.symm (e i)).1.val + 1 = i.1.val + 1
      rw [e.symm_apply_apply]
    rw [lieTreeWeight_relabel, heq]
    exact hd
  have hr' : (FreeMagma.map e a).length = r := (lieTreeLength_relabel e a).trans hr
  have hz : ∀ i, z i ∈ S (d i) := fun i => (J (e.symm i).1 (e.symm i).2).property
  have h := B.comparison_space_top_frequency D E T hbQ hT V g hg D' hfreq
    (Fintype.card (SubspaceFreeLift.Alphabet S)) d (FreeMagma.map e a) hd' hr' z hz
  have heq : z ∘ e = (fun a : SubspaceFreeLift.Alphabet S => (J a.1 a.2).val) := by
    funext i
    change (J (e.symm (e i)).1 (e.symm (e i)).2).val = (J i.1 i.2).val
    rw [e.symm_apply_apply]
  rw [lieTreeEval_relabel, heq] at h
  rw [hfreq]
  exact h

theorem CoefficientBases.native_comparison_frequency_zero
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
        (finrank ℚ (SubspaceFreeLift.Algebra S r))) (U : M.DegreeRankStructure r),
      U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      ∀ η : SubspaceFreeLift.Algebra S r →ₗ[ℚ] ℚ,
        η = (pairDifferenceFunctional V.frequency).comp
          (SubspaceFreeLift.evaluation S J
            (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS).toLinearMap →
        ∀ x ∈ U.filtration.layer s r, η x = 0 := by
  intro S hS J M U hU η hη x hx
  rw [hη]
  change pairDifferenceFunctional V.frequency (SubspaceFreeLift.evaluation S J _ hS x) = 0
  apply B.comparison_free_top_frequency D E T hbQ hT V g hg D' hTfil hfreq J x
  simpa only [hU] using hx

end Erdos3.NativeRankRelation.CommonData

end

end OAI
