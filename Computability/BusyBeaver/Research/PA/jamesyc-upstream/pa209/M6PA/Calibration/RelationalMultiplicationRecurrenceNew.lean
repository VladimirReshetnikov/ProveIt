module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRecurrenceInputs
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

def mulNewRecurrenceCase {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h base x y z : Nat) (I : MulRecurrenceInputs Γ top u c v g h base)
    (hxu : ND.Proof Γ (eq (.fvar x) (.fvar u)))
    (hyv : ND.Proof Γ (eq (.fvar y) (.fvar v)))
    (hzx : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar z) (.fvar y)) := by
  have hzu := successorTargetTransport E z x u hxu hzx
  have hzt := successorPredecessorUnique E.core u z top I.topDomain hzu I.inputSucc
  have he := edgeInputTransport E g top z c (E.symmetryOf hzt) I.endpoint
  have hh := exactPreservesEdge g h u v z c I.extension he
  have hs := mulAddTargetTransport E c base v y (E.symmetryOf hyv) I.outputAdd
  exact mulPreviousIntro h base z y c hh hs

#print axioms mulNewRecurrenceCase

end M6.PA.RelationalSource.PairGraph
