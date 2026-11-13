module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationBinderSyntax
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueVectorRealization
open NumericPAeqTerm (targetShiftTerms)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def uniformMatrix (s r b f a w p:V):V :=
  imp language (vectorInput s r b f a w)
    (imp language (⌜NumericPAeqTerm.domainTemplate⌝:V) (biCode (binderLeft b f w p) (binderRight a f p)))
theorem uniformMatrix_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    IsSemiformula language 1 (uniformMatrix s r b f a w p) := by
  have hi := input_valid h
  have hl := binderLeft_valid h
  have hr := binderRight_valid h
  exact IsSemiformula.imp.mpr ⟨⟨hi.isUFormula,le_trans hi.bv_le (by simp)⟩,
    IsSemiformula.imp.mpr ⟨by simpa using Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate,
      IsSemiformula.and.mpr ⟨IsSemiformula.imp.mpr ⟨hl,hr⟩,IsSemiformula.imp.mpr ⟨hr,hl⟩⟩⟩⟩
theorem binderLeft_free {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    free language (binderLeft b f w p)=
      substitutedFormula (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f) (qVec Presentation.language w) p := by
  have hp := IsSemiformula.all.mp h.2.2.2.1
  have hs := (freeSupported_all hp.isUFormula).mp h.2.2.2.2.2.1
  have hw := h.2.2.2.2.1.qVec
  have hws := (NumericPAeqTerm.vectorFreeSupported_qVec ⟨h.2.2.2.2.1.isUTerm,h.2.2.2.2.2.2⟩).2
  exact formulaSyntax_supported_free_binder h.1 h.2.1 (hp.subst hw) (freeSupported_subst hp hw hs hws)
theorem binderRight_free {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    free language (binderRight a f p)=
      originalFormula (qqFvar 0∷targetShiftTerms a) (targetShiftTerms f) p := by
  have hp := IsSemiformula.all.mp h.2.2.2.1
  exact formulaSyntax_supported_free_binder h.2.2.1 h.2.1 hp ((freeSupported_all hp.isUFormula).mp h.2.2.2.2.2.1)
theorem uniformMatrix_free {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    free language (uniformMatrix s r b f a w p)=
      imp language (vectorInput s r (targetShiftTerms b) (targetShiftTerms f) (targetShiftTerms a) w)
        (imp language (NumericPAeqTerm.domainCode (qqFvar 0))
          (formulaComparison (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)
            (qqFvar 0∷targetShiftTerms a) (qVec Presentation.language w) p)) := by
  have hi := input_valid h
  have hi1 : IsSemiformula language 1 (vectorInput s r b f a w) :=
    ⟨hi.isUFormula,le_trans hi.bv_le (by simp)⟩
  have hd : IsSemiformula language 1 (⌜NumericPAeqTerm.domainTemplate⌝:V) := by
    simpa using Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate
  have hl := binderLeft_valid h
  have hr := binderRight_valid h
  have hlr := IsSemiformula.imp.mpr ⟨hl,hr⟩
  have hrl := IsSemiformula.imp.mpr ⟨hr,hl⟩
  have hb : IsSemiformula language 1 (biCode (binderLeft b f w p) (binderRight a f p)) := IsSemiformula.and.mpr ⟨hlr,hrl⟩
  rw [uniformMatrix,free_imp_code hi1 (IsSemiformula.imp.mpr ⟨hd,hb⟩),
    free_zero_arity hi,input_targetShift h,free_imp_code hd hb,free_domain_code]
  simp only [biCode,free_and_code hlr hrl,free_imp_code hl hr,free_imp_code hr hl,
    binderLeft_free h,binderRight_free h,formulaComparison]
#print axioms uniformMatrix_valid
#print axioms binderLeft_free
#print axioms binderRight_free
#print axioms uniformMatrix_free
end M6.PA.NumericPAeqFormulaRealization

