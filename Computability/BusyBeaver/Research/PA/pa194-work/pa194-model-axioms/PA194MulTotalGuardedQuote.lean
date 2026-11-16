import PA194NameFactsProof
import PA194MulTotalGuardedSource
import PA194ForwardFormulaQuoteSteps
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194MulTotalGuardedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194MulRecurrenceNew PA194Schematic PA194GuardedCompiler PA194ForwardTyped PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem m1_code : (tHyp sM1 : Bootstrapping.Formula V SourceL).val = (⌜target⌝ : V) := by
  simp [tHyp,sM1,instS_sDom,instS_sMul,tDom_val,tMul_val,
    target,mulOutput,Semiformula.quote_all,Semiformula.quote_ex,Semiformula.quote_and,Semiformula.quote_or,quote_neg,Semiformula.imp_eq,
    ←domainCode_quote,←multiplicationCode_quote,multiplicationCode,Semiterm.quote_def]
#print axioms m1_code
end generic
end PA194MulTotalGuardedSource
