import PA194NameFactsProof
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
namespace PA194SourceEIQuote
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal

def target : Proposition SourceL := ∀⁰ ∀⁰ ∀⁰
  (domain (.bvar 1) 🡒 domain (.bvar 0) 🡒
    eq (.bvar 1) (.bvar 2) 🡒 eq (.bvar 0) (.bvar 2) 🡒 orderIso (.bvar 1) (.bvar 0))

theorem mapStdOne {n : Nat} (t : ST n) : (fun j : Fin 1 => (tstd (![t] j) : SyntacticSemiterm SourceL n)) = ![tstd t] := by
  funext i
  fin_cases i <;> simp

theorem mapStdTwo {n : Nat} (t u : ST n) : (fun j : Fin 2 => (tstd (![t,u] j) : SyntacticSemiterm SourceL n)) = ![tstd t,tstd u] := by
  funext i
  fin_cases i <;> simp

theorem stdDom {n : Nat} (t : ST n) : sinst tau0 (sDom t) = domain (tstd t) := by
  dsimp only [sDom,sinst,tau0,Letter.ar]
  rw [mapStdOne]
  change Semiformula.rewAux (Rew.subst ![tstd t]) (domain (.bvar 0)) = _
  rw [domain_rew]
  rfl

theorem stdEq {n : Nat} (t u : ST n) : sinst tau0 (sEq t u) = eq (tstd t) (tstd u) := by
  dsimp only [sEq,sinst,tau0,Letter.ar]
  rw [mapStdTwo]
  simp [equalityTemplate,eq,Rewriting.subst,app_eq_rewAux,Semiformula.rewAux,Rew.subst,Rew.func,Function.comp_def]
  funext i
  fin_cases i <;> rfl

theorem stdIso {n : Nat} (t u : ST n) : sinst tau0 (sIso t u) = orderIso (tstd t) (tstd u) := by
  dsimp only [sIso,sinst,tau0,Letter.ar]
  rw [mapStdTwo]
  change Semiformula.rewAux (Rew.subst ![tstd t,tstd u]) (orderIso (.bvar 0) (.bvar 1)) = _
  rw [orderIso_rew]
  rfl

theorem stdNotDom {n : Nat} (t : ST n) : sinst tau0 (∼sDom t) = ∼domain (tstd t) := by
  change sinst tau0 (Semiformula.nrel (BoxRel.box Letter.dom) ![t]) = _
  dsimp only [sinst,tau0,Letter.ar]
  rw [mapStdOne]
  change ∼(Semiformula.rewAux (Rew.subst ![tstd t]) (domain (.bvar 0))) = _
  rw [domain_rew]
  rfl

theorem stdNotEq {n : Nat} (t u : ST n) : sinst tau0 (∼sEq t u) = ∼eq (tstd t) (tstd u) := by
  change sinst tau0 (Semiformula.nrel (BoxRel.box Letter.eq) ![t,u]) = _
  dsimp only [sinst,tau0,Letter.ar]
  rw [mapStdTwo]
  have h : (equalityTemplate ⇜ ![tstd t,tstd u]) = eq (tstd t) (tstd u) := by
    have h0 := stdEq t u
    dsimp only [sEq,sinst,tau0,Letter.ar] at h0
    rw [mapStdTwo] at h0
    exact h0
  rw [h]

theorem source_quote_identity : (sinst tau0 sEI : Proposition SourceL) = target := by
  change (∀⁰ ∀⁰ ∀⁰ (sinst tau0 (∼sDom #1) ⋎
    (sinst tau0 (∼sDom #0) ⋎ (sinst tau0 (∼sEq #1 #2) ⋎
      (sinst tau0 (∼sEq #0 #2) ⋎ sinst tau0 (sIso #1 #0)))))) = _
  rw [stdNotDom,stdNotDom,stdNotEq,stdNotEq,stdIso]
  rfl

#print axioms source_quote_identity
end PA194SourceEIQuote
