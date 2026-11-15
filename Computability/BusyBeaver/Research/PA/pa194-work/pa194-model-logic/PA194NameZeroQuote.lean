import PA194TermNames
import PA194ForwardRootQuote
import PA194ClosedSentenceEnvironment
import PA194PAeqStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194NameZeroQuote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher PA194GuardedCompiler PA194ForwardTyped PA194ClosedEnvironment PA194PAeqBind
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def nameZero : Proposition PA194PAeq.language := .exs (PA194PAeq.eq (.bvar 0) PA194PAeq.zero)
theorem nameZero_quote : (⌜nameZero⌝ : V) = exName (zeroT : V) := by
  change (⌜(∃⁰ (PA194PAeq.eq (.bvar 0) PA194PAeq.zero) : Semiproposition PA194PAeq.language 0)⌝ : V) = _
  rw [Semiformula.quote_ex]
  change ^∃ (⌜(.rel PA194PAeq.Rel.eq ![.bvar 0,PA194PAeq.zero] : SourceFormula 1)⌝ : V) = _
  rw [quote_eq_rel]
  simp [exName,zeroT,PA194PAeq.zero,peq,Semiterm.quote_def]
  change ((0 : Nat) : V) = 0
  simp
#print axioms nameZero_quote
end generic
end PA194NameZeroQuote
