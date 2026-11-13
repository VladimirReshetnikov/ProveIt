module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportSubstitution
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem supported_coverage_subst {s r n param w p : V}
    (hp : ParametersValid r n param) (ht : IsSemiformula Presentation.language s p)
    (hw : IsSemitermVec Presentation.language s r w)
    (hs : FreeSupported (len (nth param 1)) p)
    (hws : ∀ i<s, NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth w i)) :
    SupportedFormulaCovered r n param (subst Presentation.language w p) :=
  ⟨hp,ht.subst hw,freeSupported_subst ht hw hs hws⟩

theorem formulaSyntax_supported_subst_isSemiformula {s r n param w p : V}
    (hp : ParametersValid r n param) (ht : IsSemiformula Presentation.language s p)
    (hw : IsSemitermVec Presentation.language s r w)
    (hs : FreeSupported (len (nth param 1)) p)
    (hws : ∀ i<s, NumericPAeqTerm.FreeSupported (len (nth param 1)) (nth w i)) :
    IsSemiformula language n (formulaSyntax param (subst Presentation.language w p)) :=
  formulaSyntax_supported_isSemiformula (supported_coverage_subst hp ht hw hs hws)
#print axioms supported_coverage_subst
#print axioms formulaSyntax_supported_subst_isSemiformula
end M6.PA.NumericPAeqFormula

