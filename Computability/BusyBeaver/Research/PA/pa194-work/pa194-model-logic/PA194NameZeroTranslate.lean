import PA194NameZeroQuote
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

theorem tr_nameZero_quote : tr (exName (zeroT : V)) =
    (⌜formula nameZero (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V) := by
  rw [←nameZero_quote]
  let p : V := ⌜nameZero⌝
  have hp : IsUFormula PA194PAeq.language p :=
    (Semiformula.quote_isSemiformula₀ nameZero).isUFormula
  have hs : shift PA194PAeq.language p = p := by
    dsimp [p]
    rw [←Semiformula.quote_shift]
    rw [syntactic_noFree_shift_fixed 0 nameZero (by decide)]
  have heq := sentence_root_packet hp hs (idParam_identity (p+1)).1 (d := p)
  have hr := root_translate_quote nameZero p (rootParameters_length p)
  change tr p = _
  rw [tr, ←heq]
  exact hr
#print axioms tr_nameZero_quote
end generic
end PA194NameZeroQuote
