module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedSubstitution
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationSyntax
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqValueVectorRealization
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def FormulaEnvironment (s r b f a w p:V):Prop :=
  IsSemitermVec language r 0 b ∧ IsSemitermVec language (len f) 0 f ∧
  IsSemitermVec language s 0 a ∧ IsSemiformula Presentation.language s p ∧
  IsSemitermVec Presentation.language s r w ∧ FreeSupported (len f) p ∧
  ∀i<s,NumericPAeqTerm.FreeSupported (len f) (nth w i)
noncomputable def substitutedFormula (b f w p:V):V :=
  formulaSyntax (parameters b f) (subst Presentation.language w p)
noncomputable def originalFormula (a f p:V):V := formulaSyntax (parameters a f) p
noncomputable def formulaComparison (b f a w p:V):V :=
  qqAnd (imp language (substitutedFormula b f w p) (originalFormula a f p))
    (imp language (originalFormula a f p) (substitutedFormula b f w p))
noncomputable def formulaCode (s r b f a w p:V):V :=
  imp language (vectorInput s r b f a w) (formulaComparison b f a w p)
theorem substitutedFormula_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    IsFormula language (substitutedFormula b f w p) := by
  apply formulaSyntax_supported_subst_isSemiformula
    (show ParametersValid r 0 (parameters b f) from by simpa [ParametersValid] using And.intro h.1 h.2.1)
    h.2.2.2.1 h.2.2.2.2.1
  · simpa using h.2.2.2.2.2.1
  · simpa using h.2.2.2.2.2.2
theorem originalFormula_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    IsFormula language (originalFormula a f p) := by
  apply formulaSyntax_supported_isSemiformula
  exact ⟨by simpa [ParametersValid] using And.intro h.2.2.1 h.2.1,h.2.2.2.1,by simpa using h.2.2.2.2.2.1⟩
theorem term_environment {s r b f a w p t:V} (h:FormulaEnvironment s r b f a w p)
    (ht:IsSemiterm Presentation.language s t) (hs:NumericPAeqTerm.FreeSupported (len f) t):
    NumericPAeqSupportedVectorRealization.SupportedVectorEnvironment s r b f a w t :=
  ⟨h.1,h.2.1,h.2.2.1,ht,h.2.2.2.2.1,hs,h.2.2.2.2.2.2⟩
theorem input_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    IsFormula language (vectorInput s r b f a w) := by
  apply NumericPAeqSupportedVectorRealization.vectorInput_valid
    (term_environment h (show IsSemiterm Presentation.language s (qqFunc 0 0 0) by simp)
      (show NumericPAeqTerm.FreeSupported (len f) (qqFunc 0 0 0) by
        exact (NumericPAeqTerm.freeSupported_func (show Presentation.language.IsFunc (0:V) 0 by simp)
          (show IsUTermVec Presentation.language (0:V) 0 by simp)).mpr (by simp)))
theorem formulaComparison_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    IsFormula language (formulaComparison b f a w p) :=
  IsSemiformula.and.mpr ⟨IsSemiformula.imp.mpr ⟨substitutedFormula_valid h,originalFormula_valid h⟩,
    IsSemiformula.imp.mpr ⟨originalFormula_valid h,substitutedFormula_valid h⟩⟩
theorem formulaCode_valid {s r b f a w p:V} (h:FormulaEnvironment s r b f a w p):
    IsFormula language (formulaCode s r b f a w p) :=
  IsSemiformula.imp.mpr ⟨input_valid h,formulaComparison_valid h⟩
#print axioms substitutedFormula_valid
#print axioms originalFormula_valid
#print axioms input_valid
#print axioms formulaCode_valid
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization

