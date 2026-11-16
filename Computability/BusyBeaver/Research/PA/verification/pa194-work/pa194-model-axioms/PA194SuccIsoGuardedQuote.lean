import PA194NameFactsProof
import PA194SuccIsoGuardedSource
import PA194ForwardFormulaQuoteSteps
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccIsoGuardedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ForwardTyped PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem s2_code : (tHyp sS2 : Bootstrapping.Formula V SourceL).val = (⌜target⌝ : V) := by
  simp [tHyp,sS2,instS_sDom,instS_sSucc,instS_sIso,tDom_val,tSucc_val,tIso_val,
    target,Semiformula.quote_all,Semiformula.quote_or,quote_neg,Semiformula.imp_eq,
    ←domainCode_quote,←successorCode_quote,←orderIsoCode_quote,Semiterm.quote_def]
#print axioms s2_code
end generic
end PA194SuccIsoGuardedSource
