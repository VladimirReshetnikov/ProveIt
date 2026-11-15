import PA194TermNames
import PA194ForwardRootQuote
import PA194ClosedSentenceEnvironment
import PA194PAeqStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194UniqZeroQuote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher PA194GuardedCompiler PA194ForwardTyped PA194ClosedEnvironment PA194PAeqBind
open M6.PA.RelationalSource
open Ordinal (Term Formula)
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def uniqZero : Proposition PA194PAeq.language := .all (.all
    (PA194PAeq.implies (PA194PAeq.eq (.bvar 1) PA194PAeq.zero)
      (PA194PAeq.implies (PA194PAeq.eq (.bvar 0) PA194PAeq.zero)
        (PA194PAeq.eq (.bvar 1) (.bvar 0)))))
theorem uniqZero_quote : (⌜uniqZero⌝ : V) = uniq (zeroT : V) := by
  change (⌜(∀⁰ ∀⁰ (PA194PAeq.implies (PA194PAeq.eq (.bvar 1) PA194PAeq.zero)
      (PA194PAeq.implies (PA194PAeq.eq (.bvar 0) PA194PAeq.zero)
        (PA194PAeq.eq (.bvar 1) (.bvar 0)))) : Semiproposition PA194PAeq.language 0)⌝ : V) = _
  rw [Semiformula.quote_all,Semiformula.quote_all]
  change ^∀ (^∀ (⌜(.or (.nrel PA194PAeq.Rel.eq ![.bvar 1,PA194PAeq.zero])
    (.or (.nrel PA194PAeq.Rel.eq ![.bvar 0,PA194PAeq.zero])
      (.rel PA194PAeq.Rel.eq ![.bvar 1,.bvar 0])) : SourceFormula 2)⌝ : V)) = _
  have hq (a b : SourceFormula 2) : (⌜(.or a b : SourceFormula 2)⌝ : V) = (⌜a⌝ : V) ^⋎ (⌜b⌝ : V) := by
    change (⌜a ⋎ b⌝ : V) = _
    exact Semiformula.quote_or a b
  rw [hq, hq, quote_eq_nrel, quote_eq_nrel, quote_eq_rel]
  simp [uniq,zeroT,PA194PAeq.zero,peq,Semiterm.quote_def]
  change ((0 : Nat) : V) = 0
  simp
#print axioms uniqZero_quote
end generic
end PA194UniqZeroQuote
