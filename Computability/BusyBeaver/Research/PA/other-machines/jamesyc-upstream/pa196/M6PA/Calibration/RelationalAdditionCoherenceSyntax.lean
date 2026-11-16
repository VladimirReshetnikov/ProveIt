module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionTrace
public import M6PA.Calibration.RelationalOrderIso
@[expose] public section

/-! The two-input coherence predicate for actual addition traces. All five
parameters are universally bound, while the induction input remains explicit.
Equality of interpreted values is order-isomorphism, never raw equality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def addCoherencePremise (x y b c r s : Term n) : Formula n :=
  Ordinal.domain y ⋏ (Ordinal.domain b ⋏ (Ordinal.domain c ⋏
    (orderIso x y ⋏ (orderIso b c ⋏ (addResult x b r ⋏ addResult y c s)))))

def addCoherencePoint (x y b c r s : Term n) : Formula n :=
  addCoherencePremise x y b c r s 🡒 orderIso r s

def addCoherence (x : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ ∀¹ ∀¹ addCoherencePoint
    (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift x)))))
    (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)

def addCoherenceProperty : Formula 1 := addCoherence (.bvar 0)

end M6.PA.RelationalSource.PairGraph
