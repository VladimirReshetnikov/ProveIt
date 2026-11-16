import PA194SuccValueCode
import PA194DomainSuccessorClosedTemplate
import PA194ForwardFormulaQuoteSteps
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher PA194ForwardTyped PA194DomainSuccessorClosedTemplate
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem succTotalCode_quote :
    (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : V) = succTotalCode := by
  change (⌜(∀⁰ (domain (.bvar 0) 🡒 (∃⁰ (domain (.bvar 0) ⋏ successor (.bvar 1) (.bvar 0)))) :
    Proposition M6.PA.RelationalSource.language)⌝ : V) = _
  rw [Semiformula.quote_all]
  change ^∀ (⌜(∼(domain (.bvar 0)) ⋎ (∃⁰ (domain (.bvar 0) ⋏ successor (.bvar 1) (.bvar 0))) :
    Semiproposition M6.PA.RelationalSource.language 1)⌝ : V) = _
  rw [Semiformula.quote_or,quote_neg,Semiformula.quote_ex,Semiformula.quote_and,
    ←domainCode_quote (.bvar (0 : Fin 1)), ←domainCode_quote (.bvar (0 : Fin 2)),
    ←successorCode_quote (.bvar (1 : Fin 2)) (.bvar (0 : Fin 2))]
  simp [succTotalCode,Semiterm.quote_def]
#print axioms succTotalCode_quote
end generic
end PA194SuccValueSchema
