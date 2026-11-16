import PA194FoundationAdditionTrace
import PA194FoundationOrderIso

/-! The two-input coherence predicate for actual addition traces. All five
parameters are universally bound, while the induction input remains explicit.
Equality of interpreted values is order-isomorphism, never raw equality. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def addCoherencePremise (x y b c r s : Term n) : Formula n :=
  Ordinal.domain y ⋏ (Ordinal.domain b ⋏ (Ordinal.domain c ⋏
    (orderIso x y ⋏ (orderIso b c ⋏ (addResult x b r ⋏ addResult y c s)))))

def addCoherencePoint (x y b c r s : Term n) : Formula n :=
  addCoherencePremise x y b c r s 🡒 orderIso r s

def addCoherence (x : Term n) : Formula n :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ addCoherencePoint
    (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift x)))))
    (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)

def addCoherenceProperty : Formula 1 := addCoherence (.bvar 0)

end M6.PA.RelationalSource.PairGraph
