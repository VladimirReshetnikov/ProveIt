module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationBinderOpening
public import M6PA.Calibration.NumericPAeqFormulaRealizationConnectives
public import M6PA.Calibration.NumericPAeqSupportedVectorBinderInputCertificate
public import M6PA.Calibration.NumericPAeqSourceCertificateMP
public import M6PA.Calibration.NumericPAeqFormulaLogicalCurry
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueTotality NumericPAeqValueVectorRealization
open NumericPAeqTerm (targetShiftTerms)
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem uniformMatrix_free_certificate {s r b f a w p:V}
    (h:FormulaEnvironment s r b f a w (qqAll p)) (ih:FormulaSupply (V:=V) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (free language (uniformMatrix s r b f a w p))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (free language (uniformMatrix s r b f a w p))+1 := by
  have hx : IsSemiterm language 0 (qqFvar (0:V)) := by simp
  have shifted := environment_targetShift h
  have body := environment_all_body shifted hx
  let H := vectorInput s r (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w
  let D := NumericPAeqTerm.domainCode (qqFvar (0:V))
  let I := vectorInput (s+1) (r+1) (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)
    (qqFvar 0∷targetShiftTerms a) (qVec Presentation.language w)
  let C := formulaComparison (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)
    (qqFvar 0∷targetShiftTerms a) (qVec Presentation.language w) p
  have hH : IsFormula language H := input_valid shifted
  have hD : IsFormula language D := NumericPAeqTerm.domainCode_isSemiformula hx
  have hI : IsFormula language I := input_valid body
  have hC : IsFormula language C := formulaComparison_valid body
  rw [uniformMatrix_free h] at hc ⊢
  apply source_certificate_mp (imp language (qqAnd H D) C) (imp language H (imp language D C)) native lo z
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hH,hD⟩,hC⟩)
    (IsSemiformula.imp.mpr ⟨hH,IsSemiformula.imp.mpr ⟨hD,hC⟩⟩) hc
  · intro native lo z hc
    apply source_implication_compose (qqAnd H D) I C native lo z
      (IsSemiformula.and.mpr ⟨hH,hD⟩) hI hC hc
    · intro native lo z hc
      have ht : IsSemiterm Presentation.language s (qqFunc 0 0 0) := by simp
      have hs : NumericPAeqTerm.FreeSupported (len (targetShiftTerms f)) (qqFunc 0 0 0) :=
        (NumericPAeqTerm.freeSupported_func (show Presentation.language.IsFunc (0:V) 0 by simp)
          (show IsUTermVec Presentation.language (0:V) 0 by simp)).mpr (by simp)
      exact NumericPAeqSupportedVectorRealization.vector_qVec_input_requested_certificate
        (term_environment shifted ht hs) hx native lo z hc
    · intro native lo z hc
      exact ih (s+1) (r+1) (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)
        (qqFvar 0∷targetShiftTerms a) (qVec Presentation.language w) body native lo z hc
  · intro native lo z hc
    exact curry_requested_certificate H D C native lo z hH hD hC hc
#print axioms uniformMatrix_free_certificate
end M6.PA.NumericPAeqFormulaRealization

