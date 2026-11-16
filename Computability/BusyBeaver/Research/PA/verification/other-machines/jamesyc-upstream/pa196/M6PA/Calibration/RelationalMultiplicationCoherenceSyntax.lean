module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationTrace
public import M6PA.Calibration.RelationalOrderIso
@[expose] public section

/-! The two-input coherence predicate for actual multiplication traces. All five
parameters are universally bound, while the induction input remains explicit.
Equality of interpreted values is order-isomorphism, never raw equality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def mulCoherencePremise (x y b c r s : Term n) : Formula n :=
  Ordinal.domain y ⋏ (Ordinal.domain b ⋏ (Ordinal.domain c ⋏
    (orderIso x y ⋏ (orderIso b c ⋏ (mulResult x b r ⋏ mulResult y c s)))))

def mulCoherencePoint (x y b c r s : Term n) : Formula n :=
  mulCoherencePremise x y b c r s 🡒 orderIso r s

def mulCoherence (x : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ ∀¹ ∀¹ mulCoherencePoint
    (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift x)))))
    (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)

def mulCoherenceProperty : Formula 1 := mulCoherence (.bvar 0)

end M6.PA.RelationalSource.PairGraph
