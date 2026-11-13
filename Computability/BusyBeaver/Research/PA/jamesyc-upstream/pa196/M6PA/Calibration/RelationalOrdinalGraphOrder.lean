module
public import M6PA.Theory
public import M6PA.Calibration.RelationalTraceGraph
@[expose] public section

/-! Local ordinal facts needed by actual arithmetic graph extension. Neither
freshness nor predecessor uniqueness uses global IR or extensionality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (EqualityProofs eqRefl eqSymm memContainer)

def successorMember {Γ : List Form} (e : EqualityProofs Γ) (a u : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar u))) :
    ND.Proof Γ (mem (.fvar u) (.fvar a)) :=
  mp (ND.orRight (eqRefl e a)) (andRight (Ordinal.successorAt a u a hs))

def successorFresh {Γ : List Form} (e : EqualityProofs Γ) (a u : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar u)))
    (hi : ND.Proof Γ (mem (.fvar a) (.fvar u) ⋎ eq (.fvar u) (.fvar a))) : ND.Proof Γ ⊥ := by
  have hm := successorMember e a u hs
  have hn := Ordinal.containerIr a (andRight ha)
  have ht := andLeft (andLeft ha)
  apply orElim hi
  · have hh := Ordinal.transitiveAt a u a (up ht (mem (.fvar a) (.fvar u))) (assumption (by simp)) (up hm _)
    exact contradiction hh (up hn _)
  · have hh := memContainer (e.up (eq (.fvar u) (.fvar a))) u a a (assumption (by simp)) (up hm _)
    exact contradiction hh (up hn _)

def successorPredecessorUnique {Γ : List Form} (e : EqualityProofs Γ) (u a b : Nat)
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (ha : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar u)))
    (hb : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar u))) :
    ND.Proof Γ (eq (.fvar a) (.fvar b)) := by
  have hua := successorMember e a u ha
  have hub := successorMember e b u hb
  have ca := mp hub (andLeft (Ordinal.successorAt a u b ha))
  have cb := mp hua (andLeft (Ordinal.successorAt b u a hb))
  have ta := Ordinal.memberTransitiveAt u a (andLeft (andRight (andLeft hu))) hua
  have ia := Ordinal.memberIrAt u a (andRight hu) hua
  apply orElim ca
  · apply orElim (up cb (mem (.fvar a) (.fvar b)))
    · have hh := Ordinal.transitiveAt a b a (up (up ta (mem (.fvar a) (.fvar b))) (mem (.fvar b) (.fvar a)))
        (assumption (by simp)) (assumption (by simp))
      exact botElim (contradiction hh (up (up ia _) _))
    · exact assumption (by simp)
  · exact eqSymm (e.up _) b a (assumption (by simp))

#print axioms successorFresh
#print axioms successorPredecessorUnique
end M6.PA.RelationalSource.PairGraph
