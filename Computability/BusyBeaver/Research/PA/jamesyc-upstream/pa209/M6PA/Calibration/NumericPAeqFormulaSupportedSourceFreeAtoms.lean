module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSourceFreeParameters
public import M6PA.Calibration.NumericPAeqFormulaSupportedAtomValidity
public import M6PA.Calibration.NumericPAeqTermSupportedSourceFree
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem atomCode_supported_sourceFree {s n param k r ts : V}
    (h : ParametersValid (s+1) n param) (ht : IsSemitermVec Presentation.language 2 (s+1) ts)
    (hf : ∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) :
    atomCode (sourceFreeParameters s param) k r (NumericPAeqTerm.sourceFreeVec s 2 ts)=
      atomCode param k r ts := by
  have h0 := atom_term_supported_covered (index:=0) (result:=1) h ht hf (by simp) (by simp)
  have h1 := atom_term_supported_covered (index:=1) (result:=0) h ht hf (by simp) (by simp)
  unfold atomCode
  rw [NumericPAeqTerm.sourceFreeVec_nth ht.isUTerm (by simp : (0:V)<2),
    NumericPAeqTerm.sourceFreeVec_nth ht.isUTerm (by simp : (1:V)<2),
    sourceFreeParameters_equality h,sourceFreeParameters_equality h,
    NumericPAeqTerm.valueSyntax_supported_sourceFree h0,
    NumericPAeqTerm.valueSyntax_supported_sourceFree h1]
#print axioms atomCode_supported_sourceFree
end M6.PA.NumericPAeqFormula

