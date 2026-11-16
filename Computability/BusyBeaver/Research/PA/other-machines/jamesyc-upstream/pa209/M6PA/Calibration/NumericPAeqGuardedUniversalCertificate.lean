module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqGuardedUniversalInput
public import M6PA.Calibration.NumericPAeqFormulaUniversalCurry
public import M6PA.Calibration.NumericPAeqFormulaLogicalCurry
@[expose] public section
namespace M6.PA.NumericPAeqGuardedUniversal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqValueTotality NumericPAeqFormula NumericPAeqFormulaLogical
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem guarded_all_requested_certificate {s b f p:V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language (s+1) p) (hs:FreeSupported (len f) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z
      (imp language (inputDomain s b f) (formulaSyntax (NumericPAeqFormula.parameters b f) (qqAll p))))
    (child:∀g l r:V,FormulaCovered 0 g l r
      (imp language (inputDomain (s+1) (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f))
        (formulaSyntax (NumericPAeqFormula.parameters (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)) p))→
      ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 g l r)
      (imp language (inputDomain (s+1) (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f))
        (formulaSyntax (NumericPAeqFormula.parameters (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)) p))+1):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (imp language (inputDomain s b f) (formulaSyntax (NumericPAeqFormula.parameters b f) (qqAll p)))+1 := by
  have hen : ParametersValid s 0 (NumericPAeqFormula.parameters b f) := by
    simpa [ParametersValid] using And.intro hb hf
  have cov : SupportedFormulaCovered (s+1) 1 (binderParameters (NumericPAeqFormula.parameters b f)) p := by
    refine ⟨by simpa using binderParameters_valid hen,hp,?_⟩
    simpa [binderParameters,NumericPAeqTerm.shiftTerms_length hf] using hs
  have hBody := formulaSyntax_supported_isSemiformula cov
  have hDom : IsSemiformula language 1 (⌜NumericPAeqTerm.domainTemplate⌝:V) := by
    simpa using FFL.FirstOrder.Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate
  rw [formulaSyntax_all _ _ hp.isUFormula] at hc ⊢
  apply guarded_universal_certificate _ _ native lo z (input_valid hb hf)
    (IsSemiformula.imp.mpr ⟨hDom,hBody⟩) hc
  intro g l r hcov
  rw [NumericPAeqFormulaRealization.free_imp_code hDom hBody,
    NumericPAeqFormulaRealization.free_domain_code,formulaSyntax_supported_free_binder hb hf hp hs,
    input_shift hb hf] at hcov ⊢
  have hbs := targetShiftTerms_valid hb
  have hfs : IsSemitermVec language (len (targetShiftTerms f)) 0 (targetShiftTerms f) := by
    simpa [targetShiftTerms_length hf] using targetShiftTerms_valid hf
  have hx : IsSemiterm language 0 (qqFvar (0:V)) := by simp
  let H := inputDomain s (targetShiftTerms b) (targetShiftTerms f)
  let D := NumericPAeqTerm.domainCode (qqFvar (0:V))
  let I := inputDomain (s+1) (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)
  let Q := formulaSyntax (NumericPAeqFormula.parameters (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)) p
  have hH := input_valid hbs hfs
  have hD := NumericPAeqTerm.domainCode_isSemiformula hx
  have hI := input_valid (hbs.adjoin hx) hfs
  have hQ : IsFormula language Q := by
    apply formulaSyntax_supported_isSemiformula (s:=s+1)
    refine ⟨?_,hp,?_⟩
    · simpa [ParametersValid] using And.intro (hbs.adjoin hx) hfs
    · simpa [Q,targetShiftTerms_length hf] using hs
  apply source_certificate_mp (imp language (qqAnd H D) Q) (imp language H (imp language D Q)) g l r
    (IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hH,hD⟩,hQ⟩)
    (IsSemiformula.imp.mpr ⟨hH,IsSemiformula.imp.mpr ⟨hD,hQ⟩⟩) hcov
  · intro g l r hc
    apply source_implication_compose (qqAnd H D) I Q g l r
      (IsSemiformula.and.mpr ⟨hH,hD⟩) hI hQ hc
    · intro g l r hc
      exact input_prepend_requested_certificate hbs hfs hx g l r hc
    · exact child
  · intro g l r hc
    exact curry_requested_certificate H D Q g l r hH hD hQ hc
#print axioms guarded_all_requested_certificate
end M6.PA.NumericPAeqGuardedUniversal

