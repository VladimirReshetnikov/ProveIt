import OAI.Combinatorics.Progressions.Fourier.SharedFreeFactorizationFrequency

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

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

theorem paired_affine_orbit_coefficient_mem_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA : ∀ d : Fin s, coefficients A.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
    (d : Fin s) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => D.CoefficientFreeLieAlgebra)).symm
      ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] ∈
      (petalComparisonSpace
        ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0))
        (fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))
        (D.coefficientFreeFiltration.layer (d.val + 1) 2)).baseChange ℝ := by
  have h₁ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
    (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) A K
  have h₂ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
    (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) (A * K) U
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one] at h₁ h₂
  have herr : coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
      (coefficients A.log (Finsupp.single () (d.val + 1)) +
        coefficients U.log (Finsupp.single () (d.val + 1))) ∈
      (D.coefficientFreeFiltration.layer (d.val + 1) 2).baseChange ℝ := by
    rw [← hTfil]
    convert ((T.filtration.layer (d.val + 1) 2).baseChange ℝ).add_mem
      (((T.filtration.layer (d.val + 1) 2).baseChange ℝ).add_mem h₂ h₁) (hK d) using 1
    abel
  have hp : ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] ∈
      petalComparisonSpace
        (((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
        ((fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
        ((D.coefficientFreeFiltration.layer (d.val + 1) 2).baseChange ℝ) := by
    apply (mem_petalComparisonSpace _ _ _ _).mpr
    constructor
    · exact Submodule.mem_sup_left (hA d)
    · apply Submodule.mem_sup.mpr
      refine ⟨_, hU d, _, herr, ?_⟩
      change coefficients U.log (Finsupp.single () (d.val + 1)) +
        (coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
          (coefficients A.log (Finsupp.single () (d.val + 1)) +
            coefficients U.log (Finsupp.single () (d.val + 1)))) =
        coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
          coefficients A.log (Finsupp.single () (d.val + 1))
      abel
  rw [← realification_petalComparisonSpace] at hp
  obtain ⟨y, hy, heq⟩ := hp
  have hy' : (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => D.CoefficientFreeLieAlgebra)).symm
      ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] = y := by
    rw [← heq]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hy']
  exact hy

end Erdos3.NativeRankRelation.CommonData

end

end OAI
