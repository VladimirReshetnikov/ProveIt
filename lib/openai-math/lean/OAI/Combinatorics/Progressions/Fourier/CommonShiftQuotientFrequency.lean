import OAI.Combinatorics.Progressions.Polynomial.CommonDependentPolynomialIntersections

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.markedShift_top_inter_le_ker (t : ℕ) (a : Fin t → ℚ) :
    markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t s 1 r ⊓
      (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t).toSubmodule ≤
      ((B.freeFrequency D).comp (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t a)).ker := by
  intro x hx
  change B.freeFrequency D (VectorPolynomial.eval a x.val.left.val) = 0
  exact B.dependentPolynomial_top_inter_le_ker D a ⟨hx.1.2, hx.2.2⟩

theorem CoefficientBases.exists_markedShift_quotient_frequency (t : ℕ) (a : Fin t → ℚ) :
    ∃ ξ : MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] ℚ,
      ∀ x ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t s 1 r,
        ξ (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) x) =
          B.freeFrequency D (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t a x) :=
  exists_quotient_functional_preserving_subspace
    (markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t s 1 r)
    (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t).toSubmodule
    ((B.freeFrequency D).comp (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a)) (B.markedShift_top_inter_le_ker D t a)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
