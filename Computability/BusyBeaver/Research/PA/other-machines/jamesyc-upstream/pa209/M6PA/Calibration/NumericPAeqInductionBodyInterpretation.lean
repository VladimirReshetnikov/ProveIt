module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionSuccessorSyntax
public import M6PA.Calibration.NumericPAeqInductionSourceBody
public import M6PA.Calibration.NumericPAeqFormulaSupportedNegation
public import M6PA.Calibration.NumericPAeqInductionStepTemplateCode
@[expose] public section
namespace M6.PA.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem formulaSyntax_imp_left {s n param p q:V}
    (hp:SupportedFormulaCovered s n param p) (hq:IsUFormula Presentation.language q):
    formulaSyntax param (imp Presentation.language p q)=imp language (formulaSyntax param p) (formulaSyntax param q) := by
  change formulaSyntax param (qqOr (neg Presentation.language p) q)=qqOr (neg language (formulaSyntax param p)) (formulaSyntax param q)
  rw [formulaSyntax_or _ _ _ hp.2.1.isUFormula.neg hq,formulaSyntax_supported_neg hp]
theorem sourceStep_interpretation {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    formulaSyntax (parameters 0 f) (qqAll (imp Presentation.language p (successorMatrix p)))=
      NumericPAeqInductionStepTemplate.sourceStepCode (property f p) (successorProperty f p) := by
  rw [formulaSyntax_all _ _ (IsSemiformula.imp.mpr ⟨hp,successorMatrix_valid hp⟩).isUFormula,
    formulaSyntax_supported_imp (property_covered hf hp hs) (property_covered hf (successorMatrix_valid hp) (successorMatrix_supported hp hs))]
  have hd := NumericPAeqTerm.domainCode_quote (V:=V) (.bvar 0 : RelationalSource.Ordinal.Term 1)
  change NumericPAeqTerm.domainCode (qqBvar 0)=(⌜NumericPAeqTerm.domainTemplate⌝:V) at hd
  simp only [guardedAllCode,NumericPAeqInductionStepTemplate.sourceStepCode,←hd,property,successorProperty]
theorem sourceStep_neg_interpretation {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    formulaSyntax (parameters 0 f) (neg Presentation.language (qqAll (imp Presentation.language p (successorMatrix p))))=
      neg language (formulaSyntax (parameters 0 f) (qqAll (imp Presentation.language p (successorMatrix p)))) := by
  have hr := successorMatrix_valid hp
  have hc := property_covered hf hp hs
  have hrc := property_covered hf hr (successorMatrix_supported hp hs)
  rw [neg_all (IsSemiformula.imp.mpr ⟨hp,hr⟩).isUFormula,formulaSyntax_exs _ _ (IsSemiformula.imp.mpr ⟨hp,hr⟩).isUFormula.neg,
    formulaSyntax_all _ _ (IsSemiformula.imp.mpr ⟨hp,hr⟩).isUFormula,formulaSyntax_supported_imp hc hrc,
    neg_guardedAllCode (IsSemiformula.imp.mpr ⟨formulaSyntax_supported_isSemiformula hc,formulaSyntax_supported_isSemiformula hrc⟩).isUFormula]
  congr 1
  simp only [Bootstrapping.imp,neg_or hp.isUFormula.neg hr.isUFormula,hp.isUFormula.neg_neg]
  rw [formulaSyntax_and _ _ _ hp.isUFormula hr.isUFormula.neg,formulaSyntax_supported_neg hrc]
  rw [neg_or (formulaSyntax_supported_isSemiformula hc).isUFormula.neg (formulaSyntax_supported_isSemiformula hrc).isUFormula, (formulaSyntax_supported_isSemiformula hc).isUFormula.neg_neg]
theorem targetIndBody_interpretation {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    formulaSyntax (parameters 0 f) (FoundationPAeqCode.targetIndBody p)=
      imp language (zeroValue f p)
        (imp language (NumericPAeqInductionStepTemplate.sourceStepCode (property f p) (successorProperty f p))
          (guardedAllCode (property f p))) := by
  have hz : IsSemitermVec Presentation.language (1:V) 0 (qqFunc 0 0 0∷0) := by simp
  have he : ParametersValid (0:V) 0 (parameters 0 f) := by simp [ParametersValid,hf]
  have hzs : ∀i<(1:V), NumericPAeqTerm.FreeSupported (len f) ((qqFunc 0 0 0∷0).[i]) := by
    intro i hi; have hi0 : i=0 := by simpa using hi
    subst i; simpa using zero_supported (len f)
  have hzc := supported_coverage_subst he hp hz (by simpa using hs) (by simpa using hzs)
  have hstep := IsSemiformula.imp.mpr ⟨hp,successorMatrix_valid hp⟩
  have hall : IsSemiformula Presentation.language (0:V) (qqAll p) := by apply IsSemiformula.all.mpr; simpa using hp
  have hstepall : IsSemiformula Presentation.language (0:V) (qqAll (imp Presentation.language p (successorMatrix p))) := by apply IsSemiformula.all.mpr; simpa using hstep
  rw [NumericPAeqInductionSourceBody.targetIndBody_eq]
  change formulaSyntax (parameters 0 f) (imp Presentation.language (subst Presentation.language (qqFunc 0 0 0∷0) p)
    (imp Presentation.language (qqAll (imp Presentation.language p (successorMatrix p))) (qqAll p)))=_
  rw [formulaSyntax_imp_left hzc (IsSemiformula.imp.mpr ⟨hstepall,hall⟩).isUFormula]
  change imp language (zeroValue f p) (formulaSyntax (parameters 0 f) (qqOr (neg Presentation.language (qqAll (imp Presentation.language p (successorMatrix p)))) (qqAll p)))=_
  rw [formulaSyntax_or _ _ _ hstepall.isUFormula.neg hall.isUFormula,
    sourceStep_neg_interpretation hf hp hs,sourceStep_interpretation hf hp hs,
    formulaSyntax_all _ _ hp.isUFormula]
  rfl
#print axioms targetIndBody_interpretation
#print axioms sourceStep_interpretation
#print axioms sourceStep_neg_interpretation
end M6.PA.NumericPAeqInductionInterpretation

