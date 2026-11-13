module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaTargetSubstConstructors
public import M6PA.Calibration.NumericPAeqFormulaTargetSubstParameters
public import M6PA.Calibration.NumericPAeqFormulaSupportedAtomValidity
public import M6PA.Calibration.NumericPAeqTermSupportedTargetSubst
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem atomCode_supported_targetSubst {s n m w param k r ts : V}
    (h : ParametersValid s n param) (ht : IsSemitermVec Presentation.language 2 s ts)
    (hw : IsSemitermVec language n m w)
    (hf : ∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) :
    subst language w (atomCode param k r ts)=atomCode (targetSubstParameters w param) k r ts := by
  have h0 := atom_term_supported_covered (index:=0) (result:=1) h ht hf (by simp) (by simp)
  have h1 := atom_term_supported_covered (index:=1) (result:=0) h ht hf (by simp) (by simp)
  unfold atomCode
  rw [equalityCode_targetSubst hw (NumericPAeqTerm.valueSyntax_supported_isSemiformula h0)
    (NumericPAeqTerm.valueSyntax_supported_isSemiformula h1),
    NumericPAeqTerm.valueSyntax_supported_targetSubst h0 hw.qVec.qVec,NumericPAeqTerm.valueSyntax_supported_targetSubst h1 hw.qVec.qVec,
    targetSubstParameters_equality h hw (by simp),targetSubstParameters_equality h hw (by simp)]
#print axioms atomCode_supported_targetSubst
end M6.PA.NumericPAeqFormula

