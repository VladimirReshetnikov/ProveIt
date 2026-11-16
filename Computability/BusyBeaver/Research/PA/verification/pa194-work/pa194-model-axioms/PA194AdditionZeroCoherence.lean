import PA194FoundationAdditionZeroLaw
import PA194OrderIsoZero
import PA194CompositionAlign
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
open PA194CompositionAlign

def isoOutputTransport {Γ : List Form} (E : FormulaEquality Γ) (u v z : Nat)
    (hev : ND.Proof Γ (eq (.fvar u) (.fvar v)))
    (hi : ND.Proof Γ (orderIso (.fvar z) (.fvar u))) : ND.Proof Γ (orderIso (.fvar z) (.fvar v)) := by
  let P : Ordinal.Formula 1 := orderIso (.fvar z) (.bvar 0)
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar u]) P) := by
    simpa [P,orderIso_rew,Rew.subst] using hi
  have hh := E.substituteOne P (.fvar u) (.fvar v) hev hp
  simpa [P,orderIso_rew,Rew.subst] using hh

def additionZeroCoherence {Γ : List Form} (E : FormulaEquality Γ)
    (x y b c r s : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hy := zeroFromIso x y hz hxy
  have er := addResultZeroOutput E x b r hz hr
  have es := addResultZeroOutput E y c s hy hs
  have hrc := isoInputTransport E b r c (E.symmetryOf er) hbc
  exact isoOutputTransport E c s r (E.symmetryOf es) hrc

#print axioms isoOutputTransport
#print axioms additionZeroCoherence
end M6.PA.RelationalSource.PairGraph
