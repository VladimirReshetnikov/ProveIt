import PA194SourceEIQuote
import PA194AdditionA2Target
import PA194AdditionTemplateRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194AdditionA2Quote
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194SourceEIQuote
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal

theorem mapStdThree {n : Nat} (t u v : ST n) :
    (fun j : Fin 3 => (tstd (![t,u,v] j) : SyntacticSemiterm SourceL n)) = ![tstd t,tstd u,tstd v] := by
  funext i
  fin_cases i <;> simp

theorem stdNotIso {n : Nat} (t u : ST n) : sinst tau0 (∼sIso t u) = ∼orderIso (tstd t) (tstd u) := by
  change sinst tau0 (Semiformula.nrel (BoxRel.box Letter.iso) ![t,u]) = _
  dsimp only [sinst,tau0,Letter.ar]
  rw [mapStdTwo]
  change ∼(Semiformula.rewAux (Rew.subst ![tstd t,tstd u]) (orderIso (.bvar 0) (.bvar 1))) = _
  rw [orderIso_rew]
  rfl

theorem stdNotAdd {n : Nat} (t u v : ST n) : sinst tau0 (∼sAdd t u v) = ∼addResult (tstd t) (tstd u) (tstd v) := by
  change sinst tau0 (Semiformula.nrel (BoxRel.box Letter.add) ![t,u,v]) = _
  dsimp only [sinst,tau0,Letter.ar]
  rw [mapStdThree]
  change ∼(Semiformula.rewAux (Rew.subst ![tstd t,tstd u,tstd v])
    (addResult (.bvar 0) (.bvar 1) (.bvar 2))) = _
  rw [addResult_rew]
  rfl

theorem source_quote_identity : (sinst tau0 sA2 : Proposition SourceL) = PA194AdditionA2Target.target := by
  change (∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰
    (sinst tau0 (∼sDom #5) ⋎ (sinst tau0 (∼sDom #4) ⋎ (sinst tau0 (∼sDom #3) ⋎
    (sinst tau0 (∼sDom #2) ⋎ (sinst tau0 (∼sDom #1) ⋎ (sinst tau0 (∼sDom #0) ⋎
    (sinst tau0 (∼sAdd #5 #4 #3) ⋎ (sinst tau0 (∼sAdd #2 #1 #0) ⋎
    (sinst tau0 (∼sIso #5 #2) ⋎ (sinst tau0 (∼sIso #4 #1) ⋎ sinst tau0 (sIso #3 #0)))))))))))) = _
  rw [stdNotDom,stdNotDom,stdNotDom,stdNotDom,stdNotDom,stdNotDom,
    stdNotAdd,stdNotAdd,stdNotIso,stdNotIso,stdIso]
  rfl

#print axioms source_quote_identity
end PA194AdditionA2Quote
