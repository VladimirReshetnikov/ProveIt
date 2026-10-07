import OAI.Combinatorics.Progressions.Estimates.FreeCoefficientCorrectionControl
import OAI.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
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
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
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

include F

theorem exists_shared_free_common_polynomial_corrections
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let L := sharedFreeCommonCorrectionBudget s Q P'
    ∃ (m : ℕ) (Γ ε ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
      CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ)) (Real.exp L) ε.log ∧
      CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
      ∀ d : Fin s,
        coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) =
          coefficients Γ.log (Finsupp.single () (d.val + 1)) +
          coefficients ε.log (Finsupp.single () (d.val + 1)) +
          coefficients ρ.log (Finsupp.single () (d.val + 1)) := by
  intro L
  obtain ⟨l, γ, e, q, hdata⟩ := D.exists_shared_free_filtered_common E T hbQ hT F V g hg D'
    hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  obtain ⟨m, hm, hmb, _hdiv, Γ, ε, ρ, hΓ, hε, hρ, hΓ0, hε0, hρ0, hbound, hgrid⟩ :=
    D.exists_native_freeCoefficient_corrections E T hTfil γ e q
      (fun d => (hdata d).2.2.2.1)
      (fun d => (hdata d).2.2.2.2.1)
      (fun d => (hdata d).2.2.2.2.2.1)
      l (fun d => (hdata d).1) (fun d => (hdata d).2.1)
      (fun d => (hdata d).2.2.2.2.2.2.2.1)
      (fun d => (hdata d).2.2.2.2.2.2.2.2)
  refine ⟨m, Γ, ε, ρ, hm, hmb, hΓ0, hε0, hρ0, hbound, hgrid, ?_⟩
  intro d
  rw [hΓ, hε, hρ, positiveUnivariate_coefficient, positiveUnivariate_coefficient,
    positiveUnivariate_coefficient]
  exact ⟨(hdata d).2.2.1, (hdata d).2.2.2.2.2.2.1⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
