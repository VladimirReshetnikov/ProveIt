import PA194PAeqSuccessorMismatch
import PA194PAeqFormulaClosure
import PA194PAeqNegation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_imp (param : V) {p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    formulaCode param (imp ℒₒᵣ p q) =
      imp PA194PAeq.language (formulaCode param p) (formulaCode param q) := by
  simp only [imp]
  rw [formulaCode_or _ _ _ hp.neg hq, formulaCode_neg param hp]

noncomputable def inductionBodyAddOne (p : V) : V :=
  imp PA194PAeq.language (substs1 PA194PAeq.language zeroCode p)
    (imp PA194PAeq.language
      (^∀ (imp PA194PAeq.language p (substs1 PA194PAeq.language (termCode arithmeticSuccVariable) p))) (^∀ p))

theorem arithmeticSuccVariable_quote :
    (⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝ : V) = arithmeticSuccVariable := by
  change ((⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1).val : V) = arithmeticSuccVariable
  simp [arithmeticSuccVariable, Bootstrapping.Arithmetic.typedNumeral,
    Bootstrapping.Arithmetic.one, Bootstrapping.Arithmetic.qqAdd, Bootstrapping.Arithmetic.oneIndex, Bootstrapping.Arithmetic.addIndex, Bootstrapping.Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
  constructor <;> decide

theorem arithmeticZero_quote :
    (⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ : V) = ^func 0 0 0 := by
  rfl

theorem formulaCode_indBodyVal (param : V) {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    formulaCode param (indBodyVal p) = inductionBodyAddOne (formulaCode param p) := by
  have hz : IsSemiterm ℒₒᵣ 0 (^func (0:V) 0 0) := by simp [original_functions]
  have hs : IsSemiterm ℒₒᵣ 1 (arithmeticSuccVariable : V) := by
    simp [arithmeticSuccVariable,original_functions]
  have hbase := IsSemiformula.substs1 hz hp
  have hnext := IsSemiformula.substs1 hs hp
  have hstep : IsUFormula ℒₒᵣ (imp ℒₒᵣ p (substs1 ℒₒᵣ arithmeticSuccVariable p)) :=
    (IsSemiformula.imp.mpr ⟨hp,hnext⟩).isUFormula
  have hbase' := hbase.isUFormula
  have hnext' := hnext.isUFormula
  have htail : IsUFormula ℒₒᵣ (imp ℒₒᵣ (^∀ (imp ℒₒᵣ p (substs1 ℒₒᵣ arithmeticSuccVariable p))) (^∀ p)) := by
    simp [imp, hstep, hp.isUFormula, hnext']
  change formulaCode param
    (imp ℒₒᵣ (substs1 ℒₒᵣ (⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝ : V) p)
      (imp ℒₒᵣ (^∀ (imp ℒₒᵣ p (substs1 ℒₒᵣ (⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝ : V) p))) (^∀ p))) = _
  rw [arithmeticZero_quote, arithmeticSuccVariable_quote]
  rw [formulaCode_imp param hbase' htail, formulaCode_imp param (by simp [hstep]) (by simp [hp.isUFormula]),
    formulaCode_all param _ hstep, formulaCode_all param _ hp.isUFormula,
    formulaCode_imp param hp.isUFormula hnext',
    formulaCode_substs1 param hp hz, formulaCode_substs1 param hp hs,
    termCode_zero]
  rfl

#print axioms formulaCode_indBodyVal
#print axioms formulaCode_imp
#print axioms arithmeticSuccVariable_quote
#print axioms arithmeticZero_quote
end generic
end PA194PAeqBind
