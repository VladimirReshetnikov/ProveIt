import PA194FoundationCompositionTransitivity
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194CompositionAlign
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def isoInputTransport (E : FormulaEquality Γ) (u v z : Nat)
    (hev : ND.Proof Γ (eq (.fvar u) (.fvar v)))
    (hi : ND.Proof Γ (orderIso (.fvar u) (.fvar z))) : ND.Proof Γ (orderIso (.fvar v) (.fvar z)) := by
  let P : Ordinal.Formula 1 := orderIso (.bvar 0) (.fvar z)
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar u]) P) := by
    simpa [P,orderIso_rew,Rew.subst] using hi
  have hh := E.substituteOne P (.fvar u) (.fvar v) hev hp
  simpa [P,orderIso_rew,Rew.subst] using hh

def alignMiddle (E : FormulaEquality Γ) (x y y' z middle : Nat)
    (hy : ND.Proof Γ (eq (.fvar y) (.fvar middle)))
    (hy' : ND.Proof Γ (eq (.fvar y') (.fvar middle)))
    (hiso : ND.Proof Γ (orderIso (.fvar y') (.fvar z))) :
    ND.Proof Γ (orderIso (.fvar y) (.fvar z)) := by
  have h := E.transitivityOf hy' (E.symmetryOf hy)
  exact isoInputTransport E y' y z h hiso
#print axioms isoInputTransport
#print axioms alignMiddle
end PA194CompositionAlign
