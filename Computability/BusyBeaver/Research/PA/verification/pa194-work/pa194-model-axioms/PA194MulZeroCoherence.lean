import PA194MulZeroOutput
import PA194OrderIsoZero
import PA194EmptyOrderIso
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def zeroCoherence {Γ : List Form} (E : FormulaEquality Γ) (x y b c r s : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) :=
  emptyOrderIso E r s (resultZeroOutput E x b r hz hr)
    (resultZeroOutput E y c s (zeroFromIso x y hz hxy) hs)
#print axioms zeroCoherence
end PA194MulRecurrenceNew
