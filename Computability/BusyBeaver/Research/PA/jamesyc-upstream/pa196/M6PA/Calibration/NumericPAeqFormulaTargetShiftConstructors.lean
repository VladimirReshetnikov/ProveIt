module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaValidity
public import M6PA.Calibration.NumericPAeqTermTargetShiftTemplates
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem equalityTail_targetShift : Rewriting.shift equalityTail = equalityTail := by
  unfold equalityTail
  change Semiformula.rewAux Rew.shift _ = _
  rw [RelationalSource.PairGraph.orderIso_rew]
  rfl

@[simp] theorem equalityTail_code_targetShift :
    shift language (⌜equalityTail⌝ : V) = ⌜equalityTail⌝ := by
  rw [← Semiformula.quote_shift, equalityTail_targetShift]

@[simp] theorem domainTemplate_code_targetShift :
    shift language (⌜NumericPAeqTerm.domainTemplate⌝ : V) = ⌜NumericPAeqTerm.domainTemplate⌝ := by
  rw [← Semiformula.quote_shift, NumericPAeqTerm.domainTemplate_targetShift]

theorem equalityCode_targetShift {a b : V}
    (ha : IsUFormula language a) (hb : IsUFormula language b) :
    shift language (equalityCode a b) = equalityCode (shift language a) (shift language b) := by
  have ht : IsUFormula language (⌜equalityTail⌝ : V) :=
    (Semiformula.quote_isSemiformula equalityTail).isUFormula
  simp [equalityCode,ha,hb,ht]

theorem guardedAllCode_targetShift {p : V} (hp : IsUFormula language p) :
    shift language (guardedAllCode p) = guardedAllCode (shift language p) := by
  have hd : IsSemiformula language 1 (⌜NumericPAeqTerm.domainTemplate⌝ : V) := by
    simpa using Semiformula.quote_isSemiformula (V:=V) NumericPAeqTerm.domainTemplate
  simp [guardedAllCode,Bootstrapping.imp,hd.isUFormula,hp,shift_neg hd]

theorem guardedExsCode_targetShift {p : V} (hp : IsUFormula language p) :
    shift language (guardedExsCode p) = guardedExsCode (shift language p) := by
  have hd : IsUFormula language (⌜NumericPAeqTerm.domainTemplate⌝ : V) :=
    (Semiformula.quote_isSemiformula NumericPAeqTerm.domainTemplate).isUFormula
  simp [guardedExsCode,hd,hp]

#print axioms equalityCode_targetShift
#print axioms guardedAllCode_targetShift
#print axioms guardedExsCode_targetShift
end M6.PA.NumericPAeqFormula

