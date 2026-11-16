import PA194NameFactsProof
import PA194SuccTotalQuote
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SourceFixedQuotes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194SuccValueSchema PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem s1_code : (tHyp sS1 : Bootstrapping.Formula V SourceL).val = succTotalCode := by
  simp [tHyp,sS1,instS_sDom,instS_sSucc,tDom_val,tSucc_val,succTotalCode,
    Bootstrapping.Semiformula.imp_def]

theorem e1_code : (tHyp sE1 : Bootstrapping.Formula V SourceL).val =
    (⌜reflexivityFormula⌝ : V) := by
  change (tHyp sE1 : Bootstrapping.Formula V SourceL).val =
    (⌜(∀⁰ (ND.eq (.bvar 0) (.bvar 0)) : Proposition M6.PA.RelationalSource.language)⌝ : V)
  rw [Semiformula.quote_all, ←equalityCode_quote (.bvar (0 : Fin 1)) (.bvar (0 : Fin 1))]
  simp [tHyp,sE1,instS_sEq,tEq_val,Semiterm.quote_def]
#print axioms s1_code
#print axioms e1_code
end generic
end PA194SourceFixedQuotes
