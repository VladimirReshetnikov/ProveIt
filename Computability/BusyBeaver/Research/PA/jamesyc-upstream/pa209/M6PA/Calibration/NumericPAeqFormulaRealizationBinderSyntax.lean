module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRealizationShift
public import M6PA.Calibration.NumericPAeqFormulaOpeningLogic
public import M6PA.Calibration.NumericPAeqFormulaLogicalCertificate
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueVectorRealization
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def binderLeft (b f w p:V):V :=
  formulaSyntax (binderParameters (parameters b f)) (subst Presentation.language (qVec Presentation.language w) p)
noncomputable def binderRight (a f p:V):V :=
  formulaSyntax (binderParameters (parameters a f)) p
theorem environment_all_body {s r b f a w p x:V} (h:FormulaEnvironment s r b f a w (qqAll p))
    (hx:IsSemiterm language 0 x):
    FormulaEnvironment (s+1) (r+1) (x∷b) f (x∷a) (qVec Presentation.language w) p := by
  have hp := IsSemiformula.all.mp h.2.2.2.1
  exact ⟨h.1.adjoin hx,h.2.1,h.2.2.1.adjoin hx,hp,h.2.2.2.2.1.qVec,
    (freeSupported_all hp.isUFormula).mp h.2.2.2.2.2.1,
    (NumericPAeqTerm.vectorFreeSupported_qVec ⟨h.2.2.2.2.1.isUTerm,h.2.2.2.2.2.2⟩).2⟩
theorem environment_exs_all {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqExs p)):
    FormulaEnvironment s r b f a w (qqAll p) := by
  have hp := IsSemiformula.exs.mp h.2.2.2.1
  exact ⟨h.1,h.2.1,h.2.2.1,IsSemiformula.all.mpr hp,h.2.2.2.2.1,
    (freeSupported_all hp.isUFormula).mpr ((freeSupported_exs hp.isUFormula).mp h.2.2.2.2.2.1),
    h.2.2.2.2.2.2⟩
theorem binderLeft_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    IsSemiformula language 1 (binderLeft b f w p) := by
  have hp := IsSemiformula.all.mp h.2.2.2.1
  have hb : ParametersValid r 0 (parameters b f) := by simpa [ParametersValid] using And.intro h.1 h.2.1
  apply formulaSyntax_supported_subst_isSemiformula
    (show ParametersValid (r+1) 1 (binderParameters (parameters b f)) from by simpa using binderParameters_valid hb) hp h.2.2.2.2.1.qVec
  · simpa [binderParameters,NumericPAeqTerm.shiftTerms_length h.2.1] using
      (freeSupported_all hp.isUFormula).mp h.2.2.2.2.2.1
  · simpa [binderParameters,NumericPAeqTerm.shiftTerms_length h.2.1] using
      (NumericPAeqTerm.vectorFreeSupported_qVec ⟨h.2.2.2.2.1.isUTerm,h.2.2.2.2.2.2⟩).2
theorem binderRight_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    IsSemiformula language 1 (binderRight a f p) := by
  have hp := IsSemiformula.all.mp h.2.2.2.1
  have ha : ParametersValid s 0 (parameters a f) := by simpa [ParametersValid] using And.intro h.2.2.1 h.2.1
  apply formulaSyntax_supported_isSemiformula
  exact ⟨by simpa using binderParameters_valid ha,hp,by
    simpa [binderParameters,NumericPAeqTerm.shiftTerms_length h.2.1] using
      (freeSupported_all hp.isUFormula).mp h.2.2.2.2.2.1⟩
theorem formulaComparison_all {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqAll p)):
    formulaComparison b f a w (qqAll p)=biCode (guardedAllCode (binderLeft b f w p)) (guardedAllCode (binderRight a f p)) := by
  have hp := IsSemiformula.all.mp h.2.2.2.1
  simp only [formulaComparison,substitutedFormula,originalFormula,biCode,binderLeft,binderRight,
    substs_all hp.isUFormula,formulaSyntax_all _ _ hp.isUFormula,
    formulaSyntax_all _ _ (hp.subst h.2.2.2.2.1.qVec).isUFormula]
theorem formulaComparison_exs {s r b f a w p:V} (h:FormulaEnvironment s r b f a w (qqExs p)):
    formulaComparison b f a w (qqExs p)=biCode (guardedExsCode (binderLeft b f w p)) (guardedExsCode (binderRight a f p)) := by
  have hp := IsSemiformula.exs.mp h.2.2.2.1
  simp only [formulaComparison,substitutedFormula,originalFormula,biCode,binderLeft,binderRight,
    substs_ex hp.isUFormula,formulaSyntax_exs _ _ hp.isUFormula,
    formulaSyntax_exs _ _ (hp.subst h.2.2.2.2.1.qVec).isUFormula]
#print axioms environment_all_body
#print axioms binderLeft_valid
#print axioms binderRight_valid
#print axioms formulaComparison_all
#print axioms formulaComparison_exs
end M6.PA.NumericPAeqFormulaRealization
