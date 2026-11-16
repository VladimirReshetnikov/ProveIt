import PA194MulZeroCoherence
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew

def premise {n : Nat} (x y b c r s : Term n) : Formula n :=
  Ordinal.domain y ⋏ (Ordinal.domain b ⋏ (Ordinal.domain c ⋏
    (orderIso x y ⋏ (orderIso b c ⋏ (mulResult x b r ⋏ mulResult y c s)))))

def point {n : Nat} (x y b c r s : Term n) : Formula n :=
  premise x y b c r s 🡒 orderIso r s

def coherence {n : Nat} (x : Term n) : Formula n :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ point
    (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift x)))))
    (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)

def property : Ordinal.Formula 1 := coherence (.bvar 0)
#print axioms coherence
end PA194MulCoherence
