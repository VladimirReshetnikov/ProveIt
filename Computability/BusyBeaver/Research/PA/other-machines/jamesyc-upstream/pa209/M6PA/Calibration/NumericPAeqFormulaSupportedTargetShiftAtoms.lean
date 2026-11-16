module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaTargetShiftConstructors
public import M6PA.Calibration.NumericPAeqFormulaTargetShiftParameters
public import M6PA.Calibration.NumericPAeqFormulaSupportedAtomValidity
public import M6PA.Calibration.NumericPAeqTermSupportedTargetShift
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem atomCode_supported_targetShift {s n param k r ts : V}
    (h : ParametersValid s n param) (ht : IsSemitermVec Presentation.language 2 s ts)
    (hf : ∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) :
    shift language (atomCode param k r ts)=atomCode (targetShiftParameters param) k r ts := by
  have h0 := atom_term_supported_covered (index:=0) (result:=1) h ht hf (by simp) (by simp)
  have h1 := atom_term_supported_covered (index:=1) (result:=0) h ht hf (by simp) (by simp)
  unfold atomCode
  rw [equalityCode_targetShift (NumericPAeqTerm.valueSyntax_supported_isSemiformula h0).isUFormula
    (NumericPAeqTerm.valueSyntax_supported_isSemiformula h1).isUFormula,
    NumericPAeqTerm.valueSyntax_supported_targetShift h0,NumericPAeqTerm.valueSyntax_supported_targetShift h1,
    targetShiftParameters_equality h,targetShiftParameters_equality h]
#print axioms atomCode_supported_targetShift
end M6.PA.NumericPAeqFormula

