module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSourceShiftParameters
public import M6PA.Calibration.NumericPAeqFormulaSupportedAtomValidity
public import M6PA.Calibration.NumericPAeqTermSupportedSourceShift
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem atomCode_supported_sourceShift {s n param k r ts x : V}
    (h : ParametersValid s n param) (ht : IsSemitermVec Presentation.language 2 s ts)
    (hf : ∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) (hx : IsSemiterm language n x) :
    atomCode (prependFreeParameters param x) k r (termShiftVec Presentation.language 2 ts)=
      atomCode param k r ts := by
  have h0 := atom_term_supported_covered (index:=0) (result:=1) h ht hf (by simp) (by simp)
  have h1 := atom_term_supported_covered (index:=1) (result:=0) h ht hf (by simp) (by simp)
  unfold atomCode
  rw [nth_termShiftVec ht.isUTerm (by simp : (0:V)<2),
    nth_termShiftVec ht.isUTerm (by simp : (1:V)<2),
    prependFreeParameters_equality h hx,prependFreeParameters_equality h hx,
    NumericPAeqTerm.valueSyntax_supported_sourceShift h0 hx.termBShift.termBShift,
    NumericPAeqTerm.valueSyntax_supported_sourceShift h1 hx.termBShift.termBShift]
#print axioms atomCode_supported_sourceShift
end M6.PA.NumericPAeqFormula

