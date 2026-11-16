import PA194FoundationAdditionZeroLaw
import PA194EmptyOrderIso
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194AddRightZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def point {n : Nat} (x e r : Term n) : Formula n :=
  (Ordinal.zero e ⋏ addResult x e r) 🡒 orderIso x r

def rightZero {n : Nat} (x : Term n) : Formula n :=
  ∀⁰ ∀⁰ point (Rew.bShift (Rew.bShift x)) (.bvar 1) (.bvar 0)

def property : Ordinal.Formula 1 := rightZero (.bvar 0)

def basePoint {Γ : List Form} (E : FormulaEquality Γ) (x e r : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (he : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar e) (.fvar r))) :
    ND.Proof Γ (orderIso (.fvar x) (.fvar r)) :=
  emptyOrderIso E x r hx (zeroTransport E e r (E.symmetryOf (addResultZeroOutput E x e r hx hr)) he)
#print axioms basePoint
end PA194AddRightZero
