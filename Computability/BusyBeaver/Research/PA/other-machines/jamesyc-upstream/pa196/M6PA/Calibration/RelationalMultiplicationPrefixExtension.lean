module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRecurrenceExtension
public import M6PA.Calibration.RelationalAdditionFrame
@[expose] public section

/-! A full multiplication prefix extends by an explicitly supplied ordinal
additive output and exact graph adjunction. No additive totality is assumed
implicitly, and every one of the five prefix clauses is retained. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult addPrefix

def mulExtendPrefix {Γ : List Form} (S : SetProofs Γ)
    (top u base z g c v h : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (ha : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v)))
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v))) :
    ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar z) (.fvar h)) := by
  let E := S.equality
  have gd := andLeft hp
  have gf := andLeft (andRight hp)
  have gr := andLeft (andRight (andRight hp))
  have gz := andLeft (andRight (andRight (andRight hp)))
  have gc := andRight (andRight (andRight (andRight hp)))
  have hu := Ordinal.successorDomain E.core E.transitive S.intersection
    (.fvar top) (.fvar u) ht hs
  have hd := successorGraphDomain E top u v g h hs gd hx
  have hf := successorFunctional E top u v g h ht hs gd gf hx
  have hr := graphRangeExtension E g h u v gr hx hv
  have hb := exactPreservesEdge g h u v z z hx gz
  have hc := mulRecurrenceExtension E top u c v g h base ⟨hu,hs,ha,he,hx,gc⟩
  exact andIntro hd (andIntro hf (andIntro hr (andIntro hb hc)))

#print axioms mulExtendPrefix
end M6.PA.RelationalSource.PairGraph
