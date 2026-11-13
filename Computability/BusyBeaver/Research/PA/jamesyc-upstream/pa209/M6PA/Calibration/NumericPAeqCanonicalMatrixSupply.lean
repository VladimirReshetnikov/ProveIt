module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqCanonicalMatrixCertificate
public import M6PA.Calibration.NumericPAeqGuardedAlls
@[expose] public section
namespace M6.PA.NumericPAeqCanonicalMatrix
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization NumericPAeqValueTotality NumericPAeqGuardedAlls
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem matrix_supply {m b p:V} (hb:IsSemiformula Presentation.language m b)
    (hs:shift Presentation.language b=b) (hp:IsSemiformula Presentation.language 1 p)
    (he:subst Presentation.language (fvarVec m) b=FoundationPAeqCode.targetIndBody p):MatrixSupply m b := by
  intro B f hB hf native lo z hc
  have hs0 :=freeSupported_zero_of_shift_fixed hb.isUFormula hs
  have hv :IsFormula language (formulaSyntax (NumericPAeqFormula.parameters B 0) b) :=
    formulaSyntax_supported_isSemiformula ⟨by simp [ParametersValid,hB],hb,by simpa using hs0⟩
  have hG :=NumericPAeqValueDomainGuard.guard_vector_isSemiformula hB
  have hF :=NumericPAeqValueDomainGuard.guard_vector_isSemiformula hf
  have he' :=formulaSyntax_closed_environment hs0 B f 0
  unfold matrixCode at hc ⊢
  rw [he'] at hc ⊢
  apply source_implication_compose (inputDomain m B f) (NumericPAeqValueDomainGuard.guard B m)
    (formulaSyntax (NumericPAeqFormula.parameters B 0) b) native lo z (IsSemiformula.and.mpr ⟨hG,hF⟩) hG hv hc
  · intro g l z _
    simpa [inputDomain] using NumericPAeqValueCoherence.source_conjunction_projection (RelationalSource.Numeric.parameters 0 g l z)
      _ _ hG.isUFormula hF.isUFormula true
  · exact matrix_certificate hB hb hs hp he
#print axioms matrix_supply
end M6.PA.NumericPAeqCanonicalMatrix

