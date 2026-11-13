module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationSyntax
public import M6PA.Calibration.NumericPAeqSupportedVectorInputShift
public import M6PA.Calibration.NumericPAeqFormulaSupportedTargetShift
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqValueVectorRealization
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_length targetShiftTerms_valid)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem environment_targetShift {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    FormulaEnvironment s r (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w p := by
  refine ⟨targetShiftTerms_valid h.1,?_,targetShiftTerms_valid h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · simpa [targetShiftTerms_length h.2.1] using targetShiftTerms_valid h.2.1
  · simpa [targetShiftTerms_length h.2.1] using h.2.2.2.2.2.1
  · simpa [targetShiftTerms_length h.2.1] using h.2.2.2.2.2.2
theorem originalFormula_targetShift {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    shift language (originalFormula a f p)=originalFormula (targetShiftTerms a) (targetShiftTerms f) p := by
  have hp : SupportedFormulaCovered s 0 (parameters a f) p :=
    ⟨by simpa [ParametersValid] using And.intro h.2.2.1 h.2.1,h.2.2.2.1,by simpa using h.2.2.2.2.2.1⟩
  simpa [originalFormula,targetShiftParameters] using formulaSyntax_supported_targetShift hp
theorem substitutedFormula_targetShift {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    shift language (substitutedFormula b f w p)=substitutedFormula (targetShiftTerms b) (targetShiftTerms f) w p := by
  have hp := supported_coverage_subst
    (show ParametersValid r 0 (parameters b f) from by simpa [ParametersValid] using And.intro h.1 h.2.1)
    h.2.2.2.1 h.2.2.2.2.1 (by simpa using h.2.2.2.2.2.1) (by simpa using h.2.2.2.2.2.2)
  simpa [substitutedFormula,targetShiftParameters] using formulaSyntax_supported_targetShift hp
theorem input_targetShift {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    shift language (vectorInput s r b f a w)=
      vectorInput s r (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w := by
  have ht : IsSemiterm Presentation.language s (qqFunc 0 0 0) := by simp
  have hs : NumericPAeqTerm.FreeSupported (len f) (qqFunc 0 0 0) :=
    (NumericPAeqTerm.freeSupported_func (show Presentation.language.IsFunc (0:V) 0 by simp)
      (show IsUTermVec Presentation.language (0:V) 0 by simp)).mpr (by simp)
  exact NumericPAeqSupportedVectorRealization.vectorInput_targetShift (term_environment h ht hs)
theorem formulaComparison_targetShift {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    shift language (formulaComparison b f a w p)=
      formulaComparison (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w p := by
  have hl := substitutedFormula_valid h
  have hr := originalFormula_valid h
  rw [formulaComparison,shift_and
    (IsSemiformula.imp.mpr ⟨hl,hr⟩).isUFormula (IsSemiformula.imp.mpr ⟨hr,hl⟩).isUFormula]
  simp only [formulaComparison,Bootstrapping.imp,
    shift_or hl.neg.isUFormula hr.isUFormula,shift_or hr.neg.isUFormula hl.isUFormula,
    shift_neg hl,shift_neg hr,originalFormula_targetShift h,substitutedFormula_targetShift h]

#print axioms originalFormula_targetShift
#print axioms substitutedFormula_targetShift
#print axioms input_targetShift
#print axioms formulaComparison_targetShift
end M6.PA.NumericPAeqFormulaRealization
