module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaRecursion
public import M6PA.Calibration.NumericPAeqFormulaSupportedCoverage
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Both real value-syntax children of an equality atom are well scoped in the
same two-binder target context. No source term is treated as a target variable. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem atom_term_supported_covered {s n param ts index result : V}
    (h : ParametersValid s n param) (ht : IsSemitermVec Presentation.language 2 s ts)
    (hf : ∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) (hi : index<2) (hr : result<2) :
    NumericPAeqTerm.SupportedTermCovered s (n+1+1) (equalityTermParameters param result) (nth ts index) := by
  refine ⟨equalityTermParameters_valid h hr,ht.nth hi,?_⟩
  simpa [equalityTermParameters,NumericPAeqTerm.shiftTerms_length h.2,
    NumericPAeqTerm.shiftTerms_length (NumericPAeqTerm.shiftTerms_isSemitermVec h.2)] using hf index hi

theorem atomCode_supported_isSemiformula {s n param k r ts : V}
    (h : ParametersValid s n param) (ht : IsSemitermVec Presentation.language 2 s ts)
    (hf : ∀i,i<2→NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth ts i)) :
    IsSemiformula language n (atomCode param k r ts) := by
  apply equalityCode_isSemiformula
  · exact NumericPAeqTerm.valueSyntax_supported_isSemiformula (atom_term_supported_covered h ht hf (by simp) (by simp))
  · exact NumericPAeqTerm.valueSyntax_supported_isSemiformula (atom_term_supported_covered h ht hf (by simp) (by simp))

#print axioms atom_term_supported_covered
#print axioms atomCode_supported_isSemiformula
end M6.PA.NumericPAeqFormula

