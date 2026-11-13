module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqCanonicalMatrixEnvironment
public import M6PA.Calibration.NumericPAeqCanonicalMatrixLogic
public import M6PA.Calibration.NumericPAeqFormulaClosedEnvironment
public import M6PA.Calibration.NumericPAeqInductionBodyCertificate
public import M6PA.Calibration.NumericPAeqCanonicalVectorInputCertificate
@[expose] public section
namespace M6.PA.NumericPAeqCanonicalMatrix
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization NumericPAeqValueTotality NumericPAeqFormulaLogical
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem matrix_certificate {m B b p:V} (hB:IsSemitermVec language m 0 B)
    (hb:IsSemiformula Presentation.language m b) (hs:shift Presentation.language b=b)
    (hp:IsSemiformula Presentation.language 1 p)
    (he:subst Presentation.language (fvarVec m) b=FoundationPAeqCode.targetIndBody p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (NumericPAeqValueDomainGuard.guard B m) (formulaSyntax (NumericPAeqFormula.parameters B 0) b))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (NumericPAeqValueDomainGuard.guard B m) (formulaSyntax (NumericPAeqFormula.parameters B 0) b))+1 := by
  have hs0 :=freeSupported_zero_of_shift_fixed hb.isUFormula hs
  have henv :=canonical_environment hB hb hs0
  have hf :IsSemitermVec language (len B) 0 B :=by simpa [hB.lh] using hB
  have hps :FreeSupported (len B) p :=by simpa [←hB.lh] using induction_property_supported hb hs he
  let G :=NumericPAeqValueDomainGuard.guard B m
  let I :=NumericPAeqValueVectorRealization.vectorInput m 0 0 B B (fvarVec m)
  let A :=substitutedFormula 0 B (fvarVec m) b
  let R :=originalFormula B B b
  have hG :IsFormula language G :=NumericPAeqValueDomainGuard.guard_vector_isSemiformula hB
  have hI :IsFormula language I :=input_valid henv
  have hA :IsFormula language A :=substitutedFormula_valid henv
  have hR :IsFormula language R :=originalFormula_valid henv
  have hBi :IsFormula language (biCode A R) :=formulaComparison_valid henv
  have hread :R=formulaSyntax (NumericPAeqFormula.parameters B 0) b :=formulaSyntax_closed_environment hs0 B B 0
  rw [←hread] at hc ⊢
  apply source_implication_compose G (qqAnd A (biCode A R)) R native lo z hG (IsSemiformula.and.mpr ⟨hA,hBi⟩) hR hc
  · intro g l z hc
    apply source_implication_pair G A (biCode A R) g l z hG hA hBi hc
    · intro g l z hc
      have hz :=NumericPAeqInductionInterpretation.guarded_induction_body_certificate hf hp hps g l z
      have he' :imp language G A=NumericPAeqInductionInterpretation.guardedInductionBodyCode B p := by
        simp only [G,A,substitutedFormula,he,NumericPAeqInductionInterpretation.guardedInductionBodyCode,NumericPAeqInductionInterpretation.freeDomain,hB.lh]
      rw [he'] at hc ⊢
      exact hz hc
    · intro g l z hc
      apply source_implication_compose G I (biCode A R) g l z hG hI hBi hc
      · exact NumericPAeqCanonicalVectorInput.canonical_input_requested_certificate hB
      · exact open_source_formula_realization_certificate henv
  · intro g l z hc
    exact useBi_requested_certificate A R g l z hA hR hc
#print axioms matrix_certificate
end M6.PA.NumericPAeqCanonicalMatrix

