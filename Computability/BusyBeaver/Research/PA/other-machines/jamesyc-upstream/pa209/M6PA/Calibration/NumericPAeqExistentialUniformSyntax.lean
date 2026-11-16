module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqExistentialOpening
public import M6PA.Calibration.NumericPAeqFormulaLogicalCurry
@[expose] public section
namespace M6.PA.NumericPAeqExistentialInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormulaRealization NumericPAeqInductionInterpretation NumericPAeqValueCoherence NumericPAeqFormulaLogical
open NumericPAeqTerm (targetShiftTerms)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def uniformMatrix (f p u:V):V :=imp language (freeDomain f)
  (imp language (valuePredicate 0 f u) (biCode (instanceFormula f p u) (property f p)))
theorem uniformMatrix_valid {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u):
    IsSemiformula language 1 (uniformMatrix f p u) := by
  have hF :=freeDomain_valid hf
  have hB :=instanceFormula_valid hf hp hu hs hus
  have hF1:IsSemiformula language 1 (freeDomain f) :=⟨hF.isUFormula,le_trans hF.bv_le (by simp)⟩
  have hB1:IsSemiformula language 1 (instanceFormula f p u) :=⟨hB.isUFormula,le_trans hB.bv_le (by simp)⟩
  have hV :=NumericPAeqTerm.valueSyntax_supported_isSemiformula (valuePredicate_covered hf hu hus)
  change IsSemiformula language 1 (valuePredicate 0 f u) at hV
  have hP :=property_valid hf hp hs
  exact IsSemiformula.imp.mpr ⟨hF1,IsSemiformula.imp.mpr ⟨hV,IsSemiformula.and.mpr
    ⟨IsSemiformula.imp.mpr ⟨hB1,hP⟩,IsSemiformula.imp.mpr ⟨hP,hB1⟩⟩⟩⟩
theorem uniformMatrix_free {f p u:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hu:IsSemiterm Presentation.language 0 u)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hus:NumericPAeqTerm.FreeSupported (len f) u):
    free language (uniformMatrix f p u)=imp language (freeDomain (targetShiftTerms f))
      (imp language (NumericPAeqTerm.valueSyntax (NumericPAeqTerm.parameters 0 (targetShiftTerms f) (qqFvar 0)) u)
        (formulaComparison 0 (targetShiftTerms f) (qqFvar 0∷0) (u∷0) p)) := by
  have hF :=freeDomain_valid hf
  have hB :=instanceFormula_valid hf hp hu hs hus
  have hF1:IsSemiformula language 1 (freeDomain f) :=⟨hF.isUFormula,le_trans hF.bv_le (by simp)⟩
  have hB1:IsSemiformula language 1 (instanceFormula f p u) :=⟨hB.isUFormula,le_trans hB.bv_le (by simp)⟩
  have hV :=NumericPAeqTerm.valueSyntax_supported_isSemiformula (valuePredicate_covered hf hu hus)
  change IsSemiformula language 1 (valuePredicate 0 f u) at hV
  have hP :=property_valid hf hp hs
  have hBP :=IsSemiformula.imp.mpr ⟨hB1,hP⟩
  have hPB :=IsSemiformula.imp.mpr ⟨hP,hB1⟩
  have hBi : IsSemiformula language 1 (biCode (instanceFormula f p u) (property f p)) := IsSemiformula.and.mpr ⟨hBP,hPB⟩
  rw [uniformMatrix,free_imp_code hF1 (IsSemiformula.imp.mpr ⟨hV,hBi⟩),
    free_zero_arity hF,freeDomain_shift hf,free_imp_code hV hBi,valuePredicate_free hf hu hus]
  change imp language _ (imp language _ (free language (qqAnd (imp language (instanceFormula f p u) (property f p)) (imp language (property f p) (instanceFormula f p u)))))=_
  rw [free_and_code hBP hPB,free_imp_code hB1 hP,free_imp_code hP hB1,
    free_zero_arity hB,instanceFormula_shift hf hp hu hs hus,property_free hf hp hs]
  rfl
#print axioms uniformMatrix_valid
#print axioms uniformMatrix_free
end M6.PA.NumericPAeqExistentialInterpretation

