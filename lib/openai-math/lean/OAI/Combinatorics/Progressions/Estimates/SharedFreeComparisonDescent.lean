import OAI.Combinatorics.Progressions.Linear.SharedFreeComparisonKernel

namespace OAI

section

namespace Erdos3

noncomputable def rankUnitDescentConstant (s : ℕ) : ℕ :=
  (RationalFilteredNilmanifold.UnitVerticalObservable.exists_lower_rank_family.{0, 0, 0} s).choose

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_lower_rank_family
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) (pM : ℝ) (hpM : 0 ≤ pM) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ [TopologicalSpace (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))]
      [T2Space (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))]
      (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1)))) (U : M.DegreeRankStructure (r + 1)),
      U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      U.ComplexityLE pM →
      ∀ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
          (Fin W.family.outputDim × Fin W.family.outputDim) pM,
        Z.frequency = (pairDifferenceFunctional V.frequency).comp
          (SubspaceFreeLift.evaluation S J
            (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS).toLinearMap →
        ∀ u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          RationalFilteredNilmanifold.HasLowerRankUnitFamily M U Z.observable u
            ((pM + rankUnitDescentConstant s) ^ rankUnitDescentConstant s) := by
  intro S hS _ _ _ _ J M U hU hUc Z hZ u
  have hzero := B.native_comparison_frequency_zero D E T hbQ hT V g hg D'
    hTfil hfreq J M U hU Z.frequency hZ
  obtain ⟨n, hn, Q', U', hQF, _, _, hU'c, hK⟩ :=
    (RationalFilteredNilmanifold.UnitVerticalObservable.exists_lower_rank_family.{0, 0, 0} s).choose_spec.2
      M U Z u hpM hUc hzero
  refine ⟨n, hn, Q', U', hU'c, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (SubspaceFreeLift.Algebra S (r + 1) ⧸ U.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (SubspaceFreeLift.Algebra S (r + 1) ⧸ U.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q'.basis
  obtain ⟨K, hKo, hKn, hKc, hKu, _, hKe⟩ := hK
  exact ⟨U.rankQuotientOrbit Q' hQF u, K, hKo, hKn, hKc, hKu, hKe⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
