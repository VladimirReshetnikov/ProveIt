module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaArity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem neg_guardedAllCode {p : V} (hp : IsUFormula language p) :
    neg language (guardedAllCode p)=guardedExsCode (neg language p) := by
  have hd : IsUFormula language (⌜NumericPAeqTerm.domainTemplate⌝ : V) :=
    (FFL.FirstOrder.Semiformula.quote_isSemiformula NumericPAeqTerm.domainTemplate).isUFormula
  simp [guardedAllCode,guardedExsCode,Bootstrapping.imp,hd,hp]

theorem neg_guardedExsCode {p : V} (hp : IsUFormula language p) :
    neg language (guardedExsCode p)=guardedAllCode (neg language p) := by
  have hd : IsUFormula language (⌜NumericPAeqTerm.domainTemplate⌝ : V) :=
    (FFL.FirstOrder.Semiformula.quote_isSemiformula NumericPAeqTerm.domainTemplate).isUFormula
  simp [guardedAllCode,guardedExsCode,Bootstrapping.imp,hd,hp]

#print axioms neg_guardedAllCode
#print axioms neg_guardedExsCode
end M6.PA.NumericPAeqFormula

